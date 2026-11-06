-- Prove2me | Definitions.Def_DRSub4633_eFace
-- name    : DRSub4633_eFace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:05:19.967411+00:00
-- url     : https://prove2.me/theorems/7fc7e054-4845-4c3d-a327-ea588c394c98
-- title:
--   The face function $e(r)=F(r,\mathbf 1_L)$
-- statement:
--   On the face where every large coordinate equals one,
--   $$e(r)=F(r,\mathbf 1_L),\qquad r\in[0,1]^S.$$
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, p.11

import Mathlib
import Definitions.Def_DRSub4633_resid
import Definitions.Def_DRSub4633_mergePt

namespace DRSub4633

/-- **The face function `e(r) = F(r, 1_L)`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, p.11: "On the face where
every large coordinate equals one, let `e(r) = F(r, 1_L)` for `r ∈ [0, 1]^S`."

**Formalization Note.** `r` is a function on `Fin n`; only its small coordinates are read. -/
noncomputable def eFace {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (r : Fin n → ℝ) : ℝ :=
  resid f x (mergePt x r (fun _ => 1))

end DRSub4633


