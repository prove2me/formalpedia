-- Prove2me | Definitions.Def_WassersteinDRO_Gelbrich_psdSqrt
-- name    : WassersteinDRO_Gelbrich_psdSqrt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:22:15.043635+00:00
-- url     : https://prove2.me/theorems/f69819d5-214a-4480-a4a4-a66cbd32122e
-- title:
--   Positive-semidefinite square root of a matrix
-- statement:
--   For a positive semidefinite matrix $A$, $\mathrm{psdSqrt}(A)$ denotes the unique positive
--   semidefinite matrix $B$ with $B B = A$ (the matrix $\Sigma^{1/2}$ notation used throughout the
--   paper, e.g. eq. (8)). Chosen by the axiom of choice over the defining existential; irrelevant
--   outside positive semidefinite inputs, which is the only case this chapter ever applies it to.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, notation Σ^{1/2} used from eq. (8), p. 8, onward

import Mathlib

open Classical

namespace WassersteinDRO.Gelbrich

/-- The positive-semidefinite square root of a matrix, `Σ^{1/2}` in the notation used
throughout this chapter (Kuhn et al. 2019, e.g. eq. (8), p. 8). For a positive semidefinite
`A`, a positive semidefinite `B` with `B*B = A` exists and is unique; `psdSqrt A` picks that
`B` by choice over the defining existential. Every use of `psdSqrt` in this chapter applies it
only to matrices hypothesized positive semidefinite (covariance matrices `Σ ∈ S^m_+`), so the
junk value `0` returned when no such `B` exists never enters a faithfulness-relevant
statement. -/
noncomputable def psdSqrt {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  if h : ∃ B : Matrix (Fin m) (Fin m) ℝ, B.PosSemidef ∧ B * B = A then h.choose else 0

end WassersteinDRO.Gelbrich


