-- Prove2me | Definitions.Def_WassersteinDRO_Guarantees_psdSqrt
-- name    : WassersteinDRO_Guarantees_psdSqrt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:30:50.843979+00:00
-- url     : https://prove2.me/theorems/745ee4ab-b9ea-4fdc-9e23-3fc5f991cab6
-- title:
--   Positive-semidefinite square root of a matrix
-- statement:
--   For a positive semidefinite matrix $A$, $\mathrm{psdSqrt}(A)$ denotes the unique positive
--   semidefinite matrix $B$ with $B B = A$ (the $\Sigma^{1/2}$ notation used throughout the paper).
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, notation used from eq. (8), p. 8, onward

import Mathlib

open Classical

namespace WassersteinDRO.Guarantees

/-- The positive-semidefinite square root of a matrix, `Σ^{1/2}`. Redefined locally in this
chapter's own namespace; see `Def_WassersteinDRO_Guarantees_meanVector` for why. -/
noncomputable def psdSqrt {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  if h : ∃ B : Matrix (Fin m) (Fin m) ℝ, B.PosSemidef ∧ B * B = A then h.choose else 0

end WassersteinDRO.Guarantees


