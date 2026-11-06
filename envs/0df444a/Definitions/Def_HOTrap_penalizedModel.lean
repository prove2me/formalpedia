-- Prove2me | Definitions.Def_HOTrap_penalizedModel
-- name    : HOTrap_penalizedModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:46:01.727332+00:00
-- url     : https://prove2.me/theorems/03345c95-200b-4c5e-957b-21da9da8033d
-- title:
--   Penalized model $\Psi$
-- statement:
--   For a target accuracy $\varepsilon>0$, a scalar model $P$ and a pivot $x$,
--   $$
--   \Psi(y):=P(y)-P(x)+\frac{3\varepsilon}4\|y-x\|_2.
--   $$
--
--   The distance penalty turns the trapping certificate into a strict boundary barrier.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Eq. (4), p.17

import Mathlib

namespace HOTrap

/-- **The penalized model** `Ψ(y) := P(y) − P(x) + (3ε/4)∥y − x∥₂`. Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Eq. (4), p.17. -/
noncomputable def penalizedModel {d : ℕ} (P : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) (ε : ℝ) (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  P y - P x + 3 * ε / 4 * ‖y - x‖

end HOTrap


