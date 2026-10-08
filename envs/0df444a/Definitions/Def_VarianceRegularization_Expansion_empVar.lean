-- Prove2me | Definitions.Def_VarianceRegularization_Expansion_empVar
-- name    : VarianceRegularization_Expansion_empVar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:28:52.458232+00:00
-- url     : https://prove2.me/theorems/2f40aac7-f706-4d7a-a2d9-58e77f67bb19
-- title:
--   Section 2.1: empirical variance
-- statement:
--   For sample values $z_1,\ldots,z_n$ with mean $\bar z$, the **empirical variance** is
--
--   $$s_n^2=\frac1n\sum_{i=1}^n z_i^2-\bar z^2.$$
--
--   This variance appears in both bounds of Theorem 1 and in its exact expansion.
--
--   **Formalization Note** Its normalization is $1/n$, as in the paper, and statements using it assume $n\ge1$.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 6, paragraph after problem (8)

import Mathlib
import Definitions.Def_VarianceRegularization_Expansion_empMean

namespace VarianceRegularization.Expansion

/-- The empirical variance `s_n²` on p. 6, normalized by `1/n` rather than `1/(n-1)`. -/
noncomputable def empVar {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, (z i) ^ 2 - (empMean z) ^ 2

end VarianceRegularization.Expansion


