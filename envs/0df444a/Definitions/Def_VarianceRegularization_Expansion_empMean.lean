-- Prove2me | Definitions.Def_VarianceRegularization_Expansion_empMean
-- name    : VarianceRegularization_Expansion_empMean
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:15:15.577962+00:00
-- url     : https://prove2.me/theorems/cbe9945c-6896-47d5-b247-a4f23675cdd1
-- title:
--   Section 2.1: empirical mean
-- statement:
--   For sample values $z_1,\ldots,z_n$, their **empirical mean** is
--
--   $$\bar z=\frac1n\sum_{i=1}^n z_i.$$
--
--   It is the center of the variance expansion.
--
--   **Formalization Note** Statements using this definition require $n\ge1$; Lean's real inverse is total at zero.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 6, paragraph after problem (8)

import Mathlib

namespace VarianceRegularization.Expansion

/-- The sample mean `z̄` on p. 6. The theorems that use it assume `0 < n`. -/
noncomputable def empMean {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, z i

end VarianceRegularization.Expansion


