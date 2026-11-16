-- Prove2me | Definitions.Def_SmoothedNash_Supplement_BoundedNorm
-- name    : SmoothedNash_Supplement_BoundedNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:57:55.779487+00:00
-- url     : https://prove2.me/theorems/f4c3a122-7b68-4585-a5d6-ec0348b979a2
-- title:
--   Assumption 1.8: $\|F(x)\| \le L_0$ on the unit ball
-- statement:
--   A map $F$ satisfies **Assumption 1.8 (bounded norm)** with constant $L_0$ if
--   $$
--   \|F(x)\| \le L_0 \qquad\text{for all } x \in B(0,1).
--   $$
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Assumption 1.8, p.5

import Mathlib
open MeasureTheory

namespace SmoothedNash.Supplement

/-- **Assumption 1.8 (Bounded norm)** (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), p.5): `‖F(x)‖ ≤ L0` for all
`x ∈ B(0,1)`. -/
def BoundedNorm {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (L0 : ℝ) :
    Prop :=
  ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, ‖F x‖ ≤ L0

end SmoothedNash.Supplement


