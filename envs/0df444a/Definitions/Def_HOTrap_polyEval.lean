-- Prove2me | Definitions.Def_HOTrap_polyEval
-- name    : HOTrap_polyEval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:45:56.972893+00:00
-- url     : https://prove2.me/theorems/554dee3e-96e9-4eb6-9773-7eb3153fa49d
-- title:
--   Evaluation of polynomials on $\mathbb R^d$
-- statement:
--   The linear map that sends a real polynomial in $d$ variables to the function it defines on $\mathbb R^d$.
--
--   It identifies polynomials with polynomial functions, as the paper does.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Appendix A, pp.53–54

import Mathlib

namespace HOTrap

/-- **Evaluation of real polynomials in `d` variables**, as a linear map from `ℝ[X₁,…,X_d]` to functions
on `ℝ^d`. Used for the polynomial spaces of Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Appendix A, pp.53–54. -/
noncomputable def polyEval (d : ℕ) : MvPolynomial (Fin d) ℝ →ₗ[ℝ] (EuclideanSpace ℝ (Fin d) → ℝ) where
  toFun P := fun y => MvPolynomial.eval (fun i => y i) P
  map_add' P Q := by
    funext y
    simp
  map_smul' a P := by
    funext y
    simp

end HOTrap


