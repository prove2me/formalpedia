-- Prove2me | Definitions.Def_PPSLattice_figCode
-- name    : PPSLattice_figCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:35:25.860165+00:00
-- url     : https://prove2.me/theorems/376efa07-9c7c-4ba4-b505-8a3952d6e433
-- title:
--   Description of the hardwired data of Figure 1
-- statement:
--   The string $(1^\lambda,N,1^n,q,\mathbf A,\mathbf s,\mathbf e,\mathbf P,\tilde{\mathbf e},tg,i,\mu,(r_j)_j)$, packed with `tup`, that a circuit compiler receives to build the circuit $C$ of Figure 1.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Construction 4.6, p.21; Figure 1, p.22

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_PPSLattice_encBin
import Definitions.Def_PPSLattice_encMat
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- The **description of the hardwired data of the circuit of Figure 1**, as handed to a circuit compiler:
`tup [1^λ, N, 1^n, q, A, s, e, P, ẽ, tg, i, µ, (r_j)_j]`, with `N`, `q`, `i`, `r_j` in binary and vectors and
matrices over `Z_q` coded entry by entry in `⌈log₂ q⌉` bits.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Construction 4.6, skEnc Step 2, p.21 ("Construct the circuit C from Figure 1"); Figure 1, p.22
("Hardwired: A, s, e, P, ẽ, tg. Also, i ∈ [N], µ ∈ {0,1}^λ"); Remark 4.9, p.22 (the randomness `r`). -/
def figCode (lam N n q : ℕ) {m : ℕ} (A : Matrix (Fin n) (Fin (Nat.clog 2 N * m)) (ZMod q))
    (s : Fin n → ZMod q) (e : Fin (Nat.clog 2 N * m) → ZMod q)
    (P : Matrix (Fin n) (Fin lam) (ZMod q)) (et tg : Fin lam → ZMod q) (i : ℕ) (mu : Str)
    (r : List ℕ) : Str :=
  BeyondDS.tup [encNat lam, encBin N, encNat n, encBin q, encMat q A, encVec q s, encVec q e,
    encMat q P, encVec q et, encVec q tg, encBin i, mu, BeyondDS.tup (r.map encBin)]

end PPSLattice


