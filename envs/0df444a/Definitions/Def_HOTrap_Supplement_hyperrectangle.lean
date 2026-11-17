-- Prove2me | Definitions.Def_HOTrap_Supplement_hyperrectangle
-- name    : HOTrap_Supplement_hyperrectangle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:29:21.599764+00:00
-- url     : https://prove2.me/theorems/42ad5a42-8191-4d8d-9703-05200d250ffc
-- title:
--   Nondegenerate compact product hyperrectangle
-- statement:
--   Given coordinate endpoints $a_i<b_i$, the **hyperrectangle** is
--   $$
--   Y=\prod_{i=1}^k[a_i,b_i]\subset\mathbb R^k.
--   $$
--   It is the sampling and optimization domain in Theorem A.10. The strict coordinate inequalities used by that theorem make it nonempty and nondegenerate.
--
--   **Formalization Note** Coordinates use the zero-based type $\operatorname{Fin}(k)$; membership is the pair of coordinatewise inequalities $a_i\le y_i\le b_i$.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Theorem A.10, p.64

import Mathlib

namespace HOTrap.Supplement

/-- The product hyperrectangle `∏ i, [a_i,b_i]` used in Theorem A.10.
Zhou--Sugiyama--Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping
Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Theorem A.10, p.64. -/
def hyperrectangle {k : ℕ} (a b : Fin k → ℝ) : Set (EuclideanSpace ℝ (Fin k)) :=
  {y | ∀ i, a i ≤ y i ∧ y i ≤ b i}

end HOTrap.Supplement


