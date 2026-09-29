-- Prove2me | Definitions.Def_HighDimProb_SparseRecovery_L1Norm
-- name    : HighDimProb_SparseRecovery_L1Norm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:10:21.52975+00:00
-- url     : https://prove2.me/theorems/24e4df9c-1678-4979-a7ba-7c19771e3580
-- title:
--   The $\ell_1$ norm of a vector
-- statement:
--   The **$\ell_1$ norm** $\|v\|_1 := \sum_i |v_i|$ of a vector $v$ indexed by a finite type — the
--   objective function of the exact-recovery program (10.12), `minimize $\|x'\|_1$ s.t. $y=Ax'$`.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Section 10.3.1, standing notation

import Mathlib

namespace HighDimProb.SparseRecovery

/-- The **`ℓ1` norm** `‖v‖₁` of a vector `v : ι → ℝ` indexed by a finite type `ι`, `∑ i, |v i|`.
Vershynin, *High-Dimensional Probability* (2018), Section 10.3.1's standing notation, used as the
objective of the recovery program (10.12) (`minimize ‖x'‖₁ s.t. y = Ax'`). -/
def l1Norm {ι : Type} [Fintype ι] (v : ι → ℝ) : ℝ :=
  ∑ i, |v i|

end HighDimProb.SparseRecovery


