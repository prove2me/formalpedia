-- Prove2me | Definitions.Def_PPSLattice_HomEval_Efficient
-- name    : PPSLattice_HomEval_Efficient
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:35:14.913538+00:00
-- url     : https://prove2.me/theorems/2585a41d-b237-4abf-b54a-3d1e219a6ccb
-- title:
--   EvalF and EvalFX run in deterministic polynomial time
-- statement:
--   One polynomial-time machine computes $\mathrm{EvalF}$ and one computes $\mathrm{EvalFX}$, on input $(q,1^n,1^m,1^\ell,\mathbf B,f)$ (and $x$), with $q$ in binary and $f$ by its description.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, Homomorphic Computation, p.16

import Mathlib
import Definitions.Def_PPSLattice_HomEval
import Definitions.Def_PPSLattice_encBin
import Definitions.Def_PPSLattice_encMat
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- EvalF and EvalFX are **deterministic polynomial-time algorithms**: one polynomial-time machine
each maps `tup [q (binary), 1^n, 1^m, 1^ℓ, code of B, code of f]` (and, for EvalFX, the input `x`) to the
code of the output matrix.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, Homomorphic Computation, p.16 ("two deterministic polynomial-time algorithms"). -/
def HomEval.Efficient (H : HomEval) : Prop :=
  (∃ M : Str → Str, PolyTimeComputable M ∧
      ∀ (q n m ell : ℕ) (B : Matrix (Fin n) (Fin (ell * m)) (ZMod q)) (f : RestrictedDec.Circuit),
        M (BeyondDS.tup [encBin q, encNat n, encNat m, encNat ell, encMat q B, f.code]) =
          encMat q (H.evalF q n m ell B f)) ∧
    ∃ M : Str → Str, PolyTimeComputable M ∧
      ∀ (q n m ell : ℕ) (B : Matrix (Fin n) (Fin (ell * m)) (ZMod q)) (f : RestrictedDec.Circuit)
        (x : Str),
        M (BeyondDS.tup [encBin q, encNat n, encNat m, encNat ell, encMat q B, f.code, x]) =
          encMat q (H.evalFX q n m ell B f x)

end PPSLattice


