-- Prove2me | Definitions.Def_CompNonlocal_ASP_advError
-- name    : CompNonlocal_ASP_advError
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:03.99196+00:00
-- url     : https://prove2.me/theorems/91888dd2-c9e2-4d5c-be84-84f13390d632
-- title:
--   A curious receiver's estimation error, Eq. (24)
-- statement:
--   For a circuit $\mathcal A$ reading the transcript and the prepared qubit,
--   $$\mathbb E\big[\|\hat r_{\mathcal A}-r(T)\|_2^2\big],\qquad \hat r_{\mathcal A}\leftarrow\mathcal A(\zeta,\mathrm{msg}_S,\mathrm{msg}_R),$$
--   with the output read as any vector of $\mathbb R^3$.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 14, Eq. (24), p.33

import Mathlib
import Definitions.Def_CompNonlocal_ASP
import Definitions.Def_CompNonlocal_decVec

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- The mean squared error of an honest-but-curious receiver's estimate in an ASP execution.
Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*,
manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 14, p.33, Eq. (24):
`E[∥r̂_A − r(T)∥₂² | (msg_S, st_S) ← ASP.Sen(1^κ), (msg_R, ζ) ← ASP.Rec(msg_S), T := (msg_S, msg_R),
r̂_A ← A_κ(ζ, msg_S, msg_R)]`.

**Formalization Note** The circuit `Adv` reads `mS ++ mR` and the prepared qubit on its quantum
input; its classical output is read as a vector of `ℝ³` by `decVec` (any vector, as in (24),
Reading 5). The sum is `Σ Pr[mS] · Re Tr(E_d ζ̃_{mS,mR}) · ‖r̂_d − r(t)‖²`. -/
noncomputable def ASP.advError (P : ASP) (κ : ℕ) (Adv : ICirc) : ℝ :=
  ∑ mS : Bits (P.Sen κ).outC.length, ∑ mR : Bits (P.Rec κ).outC.length,
    ∑ d : Bits Adv.outC.length,
      (P.senState κ (List.ofFn mS)).trace.re *
        (toQubit (Adv.effectOn 1 (List.ofFn mS ++ List.ofFn mR) (fun t => decide (t = List.ofFn d))) *
          P.prepared κ (List.ofFn mS) (List.ofFn mR)).trace.re *
        ‖decVec (List.ofFn d) - P.prepBloch κ (List.ofFn mS) (List.ofFn mR)‖ ^ 2

end CompNonlocal


