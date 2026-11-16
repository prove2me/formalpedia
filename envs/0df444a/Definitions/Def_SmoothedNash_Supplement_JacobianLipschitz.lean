-- Prove2me | Definitions.Def_SmoothedNash_Supplement_JacobianLipschitz
-- name    : SmoothedNash_Supplement_JacobianLipschitz
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:58:28.721849+00:00
-- url     : https://prove2.me/theorems/6b011295-84ca-4598-86da-42cbec5b273d
-- title:
--   Assumption 1.10: the Jacobian $J_F$ is $L_2$-Lipschitz on the unit ball
-- statement:
--   A map $F$ satisfies **Assumption 1.10 (smoothness)** with constant $L_2$ if $F$ is differentiable on $B(0,1)$ and its Jacobian is $L_2$-Lipschitz in operator norm:
--   $$
--   \|J_F(x) - J_F(y)\|_{\mathrm{op}} \le L_2 \|x - y\| \qquad\text{for all } x, y \in B(0,1).
--   $$
--
--   **Formalization Note** The Jacobian on the closed ball is the derivative within the ball (`fderivWithin`), which depends only on the values of $F$ on the ball and is unique also at boundary points, since the ball is convex with nonempty interior.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Assumption 1.10, p.5

import Mathlib
open MeasureTheory

namespace SmoothedNash.Supplement

/-- **Assumption 1.10 (Smoothness: Lipschitzness of the Jacobian)** (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), p.5):
`F` is differentiable on `B(0,1)` and its Jacobian `J_F` is `L2`-Lipschitz in operator norm:
`‖J_F(x) − J_F(y)‖_op ≤ L2 ‖x − y‖` for all `x, y ∈ B(0,1)`.

**Formalization Note** The Jacobian on the closed ball is the derivative within the ball,
`fderivWithin ℝ F (closedBall 0 1) x`, so it depends only on the values of `F` on the ball (the ball
is convex with nonempty interior, so this derivative is unique, also at boundary points).
Differentiability on the ball is presupposed by the paper's "the Jacobian `J_F(x)`". -/
def JacobianLipschitz {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (L2 : ℝ) : Prop :=
  DifferentiableOn ℝ F (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) ∧
    ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
      ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
        ‖fderivWithin ℝ F (Metric.closedBall 0 1) x - fderivWithin ℝ F (Metric.closedBall 0 1) y‖
          ≤ L2 * ‖x - y‖

end SmoothedNash.Supplement


