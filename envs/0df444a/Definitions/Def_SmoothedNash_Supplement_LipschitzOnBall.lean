-- Prove2me | Definitions.Def_SmoothedNash_Supplement_LipschitzOnBall
-- name    : SmoothedNash_Supplement_LipschitzOnBall
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:58:14.598761+00:00
-- url     : https://prove2.me/theorems/655bca01-caec-4bf1-84c3-b5d216781485
-- title:
--   Assumption 1.9: $F$ is $L_1$-Lipschitz on the unit ball
-- statement:
--   A map $F$ satisfies **Assumption 1.9 (Lipschitzness)** with constant $L_1$ if
--   $$
--   \|F(x) - F(y)\| \le L_1 \|x - y\| \qquad\text{for all } x, y \in B(0,1).
--   $$
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Assumption 1.9, p.5, and Assumption 3.1, p.21

import Mathlib
open MeasureTheory

namespace SmoothedNash.Supplement

/-- **Assumption 1.9 (Lipschitzness)** (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), p.5; Assumption 3.1, p.21):
`‖F(x) − F(y)‖ ≤ L1 ‖x − y‖` for all `x, y ∈ B(0,1)`. -/
def LipschitzOnBall {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (L1 : ℝ) :
    Prop :=
  ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
    ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, ‖F x - F y‖ ≤ L1 * ‖x - y‖

end SmoothedNash.Supplement


