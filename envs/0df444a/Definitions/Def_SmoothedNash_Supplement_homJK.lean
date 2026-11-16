-- Prove2me | Definitions.Def_SmoothedNash_Supplement_homJK
-- name    : SmoothedNash_Supplement_homJK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:02:25.623424+00:00
-- url     : https://prove2.me/theorems/b1f4f30a-a2e1-44bd-82e2-c8f91d785297
-- title:
--   Homotopy Jacobian $J_K(x,t) = [(1-t)I - tJ_F(x)/a \mid -x - F(x)/a]$
-- statement:
--   The **homotopy Jacobian** is the $n \times (n+1)$ matrix
--   $$
--   J_K(x,t) = \Bigl[\, (1-t) I - \tfrac{t}{a} J_F(x) \;\Bigm|\; -x - \tfrac{F(x)}{a} \,\Bigr].
--   $$
--   This definition applies it to a vector $w = (\bar w, s) \in \mathbb R^n \times \mathbb R$:
--   $J_K(x,t)\, w = (1-t)\bar w - \tfrac{t}{a} J_F(x)\bar w - s\,(x + F(x)/a)$.
--
--   **Formalization Note** $J_F$ is the derivative within the closed unit ball.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), §4.1.2, p.26

import Mathlib
open MeasureTheory

namespace SmoothedNash.Supplement

/-- The homotopy Jacobian `J_K(x, t) = [(1 − t) I − t J_F(x)/a | −x − F(x)/a]`
(Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), §4.1.2, p.26), an `n × (n+1)` matrix, applied to a vector `w = (w̄, s) ∈ ℝ^n × ℝ`:
`J_K(x,t) w = (1 − t) w̄ − (t/a) J_F(x) w̄ − s (x + F(x)/a)`.

**Formalization Note** `J_F(x)` is `fderivWithin ℝ F (closedBall 0 1) x` (see `JacobianLipschitz`).
`a = L0 + L1` is the argument `a`. -/
noncomputable def homJK {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (a : ℝ) (p w : EuclideanSpace ℝ (Fin n) × ℝ) : EuclideanSpace ℝ (Fin n) :=
  (1 - p.2) • w.1 - (p.2 / a) • fderivWithin ℝ F (Metric.closedBall 0 1) p.1 w.1
    - w.2 • (p.1 + a⁻¹ • F p.1)

end SmoothedNash.Supplement


