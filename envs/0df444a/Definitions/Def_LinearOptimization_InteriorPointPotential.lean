-- Prove2me | Definitions.Def_LinearOptimization_InteriorPointPotential
-- name    : LinearOptimization_InteriorPointPotential
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-06T14:45:49.735916+00:00
-- url     : https://prove2.me/theorems/70f31513-729e-40a2-986c-40354fb0b5f6
-- title:
--   Primal-dual potential function $G(x,s) = q\log s^T x - \sum_j \log x_j - \sum_j \log s_j$
-- statement:
--   The primal-dual potential function of Bertsimas & Tsitsiklis, §9.3 (p. 409):
--
--   $$G(x,s) = q\log(s^T x) - \sum_{j=1}^n \log x_j - \sum_{j=1}^n \log s_j,$$
--
--   with parameter $q > n$ and $\log$ the natural logarithm. Consumed by Theorem 9.4 (potential reduction implies an explicit iteration bound).
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, §9.3, p. 409

import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
The primal-dual potential function of §9.3.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997, §9.3 p. 409: the potential
`G(x, s) = q log s'x − ∑ⱼ log xⱼ − ∑ⱼ log sⱼ` with parameter `q > n`
(`log` = natural logarithm). Used by Bertsimas & Tsitsiklis, Theorem 9.4
(`LinearOptimization.interior_point_potential_reduction`, Mission XII).
-/

open Matrix

namespace LinearOptimization

/-- **Bertsimas & Tsitsiklis, §9.3 (p. 409).** The primal-dual potential function
`G(x, s) = q log s'x − ∑ⱼ log xⱼ − ∑ⱼ log sⱼ`. -/
noncomputable def interiorPointPotential {n : ℕ} (q : ℝ)
    (x s : Fin n → ℝ) : ℝ :=
  q * Real.log (s ⬝ᵥ x) - ∑ j, Real.log (x j) - ∑ j, Real.log (s j)

end LinearOptimization


