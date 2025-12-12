#!/usr/bin/env python3
import argparse, json, os, secrets, shutil
from typing import List
from functools import reduce

MOD = 21888242871839275222246405745257275088548364400416034343698204186575808495617

G = 5


def modinv(a, m=MOD):
    return pow(a, m-2, m)

def safe_write(path: str, data: bytes):
    tmp = path + ".tmp"
    with open(tmp, "wb") as f:
        f.write(data)
        f.flush(); os.fsync(f.fileno())
    os.replace(tmp, path)

def secure_delete(path: str):
    try:
        if os.path.exists(path):
            size = os.path.getsize(path)
            with open(path, "r+b") as f:
                f.write(b"\x00" * size)
                f.flush(); os.fsync(f.fileno())
            os.remove(path)
    except Exception:
        try:
            os.remove(path)
        except Exception:
            pass

def init_mpc(participants: int, degree: int, out_path: str):
    print(f"[MPC] жди {participants} participants, degree={degree}")
    contributions = []
    for i in range(participants):
        ri = secrets.randbelow(MOD)
        contributions.append(ri)
        print(f"  participant {i+1}: contributed random r_i (kept secret and not stored)")

    s = sum(contributions) % MOD
    s_pows = [1]
    for k in range(1, degree+1):
        s_pows.append((s_pows[-1] * s) % MOD)
    srs = [pow(G, sp, MOD) for sp in s_pows]
    payload = {
        "degree": degree,
        "srs": [str(x) for x in srs],
        "note": ""
    }
    safe_write(out_path, json.dumps(payload, indent=2).encode())
    print(f"[MPC] SRS written to {out_path}")

    for i in range(len(contributions)):
        contributions[i] = 0
    s = 0

    print("[MPC] Local secrets erased (simulated). If you wrote temp files, securely delete them.")
    return out_path
def build_example_r1cs():
    A = [[0, 1, 1, 0]]
    B = [[1, 0, 0, 0]]
    C = [[0, 0, 0, 1]]
    public_inputs = [3+4]
    witness = [None, 3, 4, 7]
    return A, B, C, public_inputs, witness

def lagrange_eval_at_s(i: int, m: int, s_val: int):
    ti = i+1
    num = 1
    den = 1
    for j in range(1, m+1):
        if j == ti: continue
        num = (num * (s_val - j)) % MOD
        den = (den * (ti - j)) % MOD
    return (num * modinv(den)) % MOD

def eval_qap_at_s(A, B, C, witness, s_val):
    m = len(A)
    nvars = len(A[0])
    def build_poly_eval(M):
        vals = [0]*m
        for i in range(m):
            Li = lagrange_eval_at_s(i, m, s_val)
            vals[i] = Li
        A_k_s = [0]*nvars
        for k in range(nvars):
            acc = 0
            for i in range(m):
                acc = (acc + (M[i][k] * vals[i])) % MOD
            A_k_s[k] = acc
        As = 0
        for k in range(nvars):
            wk = 0 if witness[k] is None else witness[k]
            As = (As + (wk * A_k_s[k])) % MOD
        return As
    As = build_poly_eval(A)
    Bs = build_poly_eval(B)
    Cs = build_poly_eval(C)
    return As, Bs, Cs

def create_proof(srs_path: str, out_proof: str):
    with open(srs_path, "rb") as f:
        srs_obj = json.load(f)
    degree = srs_obj["degree"]

    srs_list = [int(x) for x in srs_obj["srs"]]
    sim_s = srs_obj.get("sim_s")
    if sim_s is None:
        raise RuntimeError("srs.json must include 'sim_s' field for this demo (this sim stores s temporarily).")
    s_val = int(sim_s) % MOD

    A, B, C, public_inputs, witness = build_example_r1cs()
    As, Bs, Cs = eval_qap_at_s(A, B, C, witness, s_val)
    m = len(A)
    ts = 1
    for i in range(1, m+1):
        ts = (ts * (s_val - i)) % MOD
    P_s = (As * Bs - Cs) % MOD
    if ts % MOD == 0:
        raise RuntimeError("t(s) == 0 mod MOD (bad s), choose different s in init_mpc.")
    Hs = (P_s * modinv(ts)) % MOD
    proof = {
        "A_s": str(As),
        "B_s": str(Bs),
        "C_s": str(Cs),
        "H_s": str(Hs),
        "public_inputs": [str(x) for x in public_inputs],
        "note": "SIMULATED proof (contains raw field evals)."
    }
    safe_write(out_proof, json.dumps(proof, indent=2).encode())
    print(f"[PROVER] Proof written to {out_proof}")
    srs_obj.pop("sim_s", None)
    safe_write(srs_path, json.dumps(srs_obj, indent=2).encode())
    print("[PROVER] Removed sim_s from srs file (simulated key erasure).")
    return out_proof

def verify_proof(srs_path: str, proof_path: str):
    with open(srs_path, "rb") as f:
        srs_obj = json.load(f)
    with open(proof_path, "rb") as f:
        proof = json.load(f)

    sim_s = srs_obj.get("sim_s")
    if sim_s is None:
        raise RuntimeError("srs.json must contain 'sim_s' in this demo for verification (simulation).")
    s_val = int(sim_s) % MOD
    As = int(proof["A_s"])
    Bs = int(proof["B_s"])
    Cs = int(proof["C_s"])
    Hs = int(proof["H_s"])
    m = len(build_example_r1cs()[0])
    ts = 1
    for i in range(1, m+1):
        ts = (ts * (s_val - i)) % MOD
    lhs = (As * Bs - Cs) % MOD
    rhs = (Hs * ts) % MOD
    ok = (lhs == rhs)
    print("[VERIFIER] Check: A(s)*B(s) - C(s) == H(s)*t(s) ? ->", ok)
    return ok

def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd")
    p_init = sub.add_parser("init_mpc")
    p_init.add_argument("--participants", type=int, default=3)
    p_init.add_argument("--degree", type=int, default=8)
    p_init.add_argument("--out", type=str, default="srs.json")
    p_prove = sub.add_parser("prove")
    p_prove.add_argument("--srs", type=str, default="srs.json")
    p_prove.add_argument("--out", type=str, default="proof.json")
    p_verify = sub.add_parser("verify")
    p_verify.add_argument("--srs", type=str, default="srs.json")
    p_verify.add_argument("--proof", type=str, default="proof.json")
    args = ap.parse_args()

    if args.cmd == "init_mpc":
        participants = args.participants
        degree = args.degree
        contributions = [secrets.randbelow(MOD) for _ in range(participants)]
        s = sum(contributions) % MOD
        s_pows = [1]
        for k in range(1, degree+1):
            s_pows.append((s_pows[-1] * s) % MOD)
        srs = [pow(G, sp, MOD) for sp in s_pows]
        payload = {"degree": degree, "srs": [str(x) for x in srs], "sim_s": str(s),
                   "note": "SIMULATION: sim_s stored temporarily for demo — remove in real MPC."}
        safe_write(args.out, json.dumps(payload, indent=2).encode())
        for i in range(len(contributions)):
            contributions[i] = 0
        s = 0
        print(f"[init_mpc] Wrote SRS to {args.out} (sim_s present for demo). Secrets wiped from memory.")
    elif args.cmd == "prove":
        create_proof(args.srs, args.out)
    elif args.cmd == "verify":
        ok = verify_proof(args.srs, args.proof)
        print("Verification result:", ok)
    else:
        ap.print_help()

if __name__ == "__main__":
    main()
