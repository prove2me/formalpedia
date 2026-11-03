-- Prove2me | Definitions.Def_MonoInclCLC_IsClosedLoopSolution
-- name    : MonoInclCLC_IsClosedLoopSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:19:22.128983+00:00
-- url     : https://prove2.me/theorems/2a719721-f189-4ae0-a98f-50d691c37f25
-- title:
--   Eq. (1.3)–(1.4), p.3 — solutions of the closed-loop control system
-- statement:
--   A pair $(x,\lambda)$ of functions on a time set $T$ is a **solution of the closed-loop control system** if, at every $t\in T$, one has $\lambda(t)>0$ and
--   $$
--   \dot x(t)=(I+\lambda(t)A)^{-1}x(t)-x(t),\qquad \lambda(t)\,\big\|(I+\lambda(t)A)^{-1}x(t)-x(t)\big\|^{p-1}=\theta.
--   $$
--   The derivative is taken within $T$, so it is one-sided at an endpoint. A global solution is the case $T=[0,+\infty)$, and a solution on $[0,t_0]$ is the case $T=[0,t_0]$.
--
--   For $p=1$ the second equation reads $\lambda\equiv\theta$, and the system is the continuous-time proximal point flow. For larger $p$ the step size is fed back from the current state, and this is the source of the accelerated rates.
--
--   **Formalization Note** The resolvent is the family $J$ with $J_l=(I+lA)^{-1}$ for $l>0$; each theorem assumes $J$ is the resolvent, so $A$ does not appear in this definition. The exponent $p-1$ is a natural-number power, and each theorem assumes $p\ge 1$. No continuity of $\dot x$ or Lipschitz continuity of $\lambda$ is required: they are conclusions in the paper.
-- source:
--   Lin, Jordan, Monotone Inclusions, Acceleration and Closed-Loop Control, arXiv:2111.08093v4, Eq. (1.3) and Eq. (1.4), p.3; compact form with ‖(I + λ(t)A)⁻¹x(t) − x(t)‖, p.5; (x, λ) : [0, t0] ↦ H × (0, +∞), Theorem 2.4, p.6

import Mathlib

namespace MonoInclCLC

/-- **The closed-loop control system** (1.3)–(1.4) (Lin, Jordan, *Monotone Inclusions, Acceleration and Closed-Loop Control*, arXiv:2111.08093v4, Eq. (1.3), Eq. (1.4), p.3; compact form
p.5): `(x, lam)` solves `ẋ(t) + x(t) - (I + λ(t)A)⁻¹x(t) = 0`, `λ(t)‖ẋ(t)‖^(p-1) = θ`, with
`λ(t) > 0`, at every time of the time set `T`.

**Formalization Note.** `J` is the resolvent family: `J l = (I + l A)⁻¹` for `l > 0`; every theorem
carries the hypothesis `∀ l, 0 < l → IsResolvent l A (J l)`, so `A` does not appear here. `T` is
`Set.Ici 0` for a global solution `[0, +∞) ↦ H × (0, +∞)` and `Set.Icc 0 t₀` for a solution on
`[0, t₀]`; `HasDerivWithinAt … T t` is the one-sided derivative at an endpoint. The algebraic
equation is written with `‖J (lam t) (x t) - x t‖`, the paper's own form on p.5, equal to `‖ẋ(t)‖`
by the first equation. The exponent `p - 1` is a natural power (every theorem assumes `1 ≤ p`):
for `p = 1` the equation reads `lam t = θ`, as the paper says on p.3. No `C¹` or Lipschitz
requirement is imposed: those are conclusions of the paper's Theorem 2.4. -/
def IsClosedLoopSolution {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (J : ℝ → H → H) (p : ℕ) (θ : ℝ) (T : Set ℝ) (x : ℝ → H) (lam : ℝ → ℝ) : Prop :=
  ∀ t ∈ T, 0 < lam t ∧ HasDerivWithinAt x (J (lam t) (x t) - x t) T t ∧
    lam t * ‖J (lam t) (x t) - x t‖ ^ (p - 1) = θ

end MonoInclCLC


