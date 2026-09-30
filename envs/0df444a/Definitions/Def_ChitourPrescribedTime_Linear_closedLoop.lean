-- Prove2me | Definitions.Def_ChitourPrescribedTime_Linear_closedLoop
-- name    : ChitourPrescribedTime_Linear_closedLoop
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:58:26.774953+00:00
-- url     : https://prove2.me/theorems/d632d179-b105-4e70-8f06-7785ce26e339
-- title:
--   Integral-form solutions and the two closed loops: $y'=(aD_{\mathbf r}+J_n)y+(bu+d)e_n$ with $u=-K^TD^{\mathbf r}_\eta y$, and (1) with $u=-K^TD^{\mathbf r}_{\eta\lambda(t)}x$
-- statement:
--   A **solution in integral form** (Carathéodory solution) of $x' = F(t,x)$ on a time set $I$ containing $0$ is a function $x$ such that, for every $t\in I$, the map $r\mapsto F(r,x(r))$ is Lebesgue integrable on $[0,t]$ and
--   $$x(t) = x(0) + \int_0^t F(r, x(r))\,dr .$$
--
--   Two vector fields are used with this notion. Let $a,b,d:\mathbb R\to\mathbb R$, $K\in\mathbb R^n$ and $\eta\in\mathbb R$.
--
--   1. The **transformed closed loop** (equation (11) closed by the feedback $u=-K^T D^{\mathbf r}_\eta y$, i.e. system (13) of the paper) is
--   $$F_S(s, y) = \big(a(s) D_{\mathbf r} + J_n\big) y + \big(-b(s)\,K^T D^{\mathbf r}_\eta y + d(s)\big) e_n .$$
--   2. The **original closed loop** (the perturbed chain of integrators (1) closed by the time-varying feedback (22), $u(t) = -K^T D^{\mathbf r}_{\eta\lambda(t)} x(t)$, with $\lambda(t) = 1/\int_t^T a$) is
--   $$F_T(t, x) = J_n x + \big(d(t) - b(t)\,K^T D^{\mathbf r}_{\eta\lambda(t)} x\big) e_n .$$
--
--   The perturbations $b$ and $d$ are only measurable in the paper, so trajectories are absolutely continuous and satisfy the differential equation almost everywhere. The integral form states exactly that.
--
--   **Formalization Note** `IsIntegralSolution F x I` requires, for every `t ∈ I`, the `IntervalIntegrable` hypothesis on `[0, t]` together with the integral identity. The integrability clause is part of the definition because a Bochner integral of a non-integrable function is $0$ in Lean. The missions use `I = [0, ∞)` for the transformed system and `I = [0, T)` for the original one.
-- source:
--   Chitour, Ushirobira, Bouhemou, Stabilization for a Perturbed Chain of Integrators in Prescribed Time, SIAM J. Control Optim. 58 (2020), p. 1022, eq. (1); p. 1025, §2 (measurable disturbances); p. 1028, eq. (13); p. 1029, Proposition 12; p. 1030, Corollary 14, eq. (22)

import Mathlib
import Definitions.Def_ChitourPrescribedTime_Linear_chain
import Definitions.Def_ChitourPrescribedTime_Linear_timeChange

namespace ChitourPrescribedTime.Linear

open Matrix

/-- A (Carathéodory) solution in integral form of `x' = F(t, x)` on the time set `I` (which
contains `0`): for every `t ∈ I` the map `r ↦ F(r, x(r))` is Lebesgue integrable on `[0, t]` and
`x(t) = x(0) + ∫_0^t F(r, x(r)) dr`. -/
def IsIntegralSolution {n : ℕ} (F : ℝ → (Fin n → ℝ) → (Fin n → ℝ)) (x : ℝ → Fin n → ℝ)
    (I : Set ℝ) : Prop :=
  ∀ t ∈ I, IntervalIntegrable (fun r => F r (x r)) MeasureTheory.volume 0 t ∧
    x t = x 0 + ∫ r in (0)..t, F r (x r)

/-- The right-hand side of the transformed dynamics (11), `y' = (a(s) D_r + J_n) y + (b(s) u + d(s)) e_n`,
closed by the state feedback `u = -Kᵀ D^r_η y` (§3.1, (13) and Proposition 12). -/
noncomputable def feedbackFieldS (n : ℕ) (a b d : ℝ → ℝ) (K : Fin n → ℝ) (η : ℝ) :
    ℝ → (Fin n → ℝ) → (Fin n → ℝ) :=
  fun r v => a r • (Dr n *ᵥ v) + jordanBlock n *ᵥ v +
    (b r * (-(K ⬝ᵥ (dil n η *ᵥ v))) + d r) • eN n

/-- The right-hand side of the perturbed chain of integrators (1),
`ẋ = J_n x + (d(t) + b(t) u(t)) e_n`, closed by the time-varying feedback (22),
`u(t) = -Kᵀ D^r_{η λ(t)} x(t)`, with `λ` from (21). -/
noncomputable def feedbackFieldT (n : ℕ) (T : ℝ) (a b d : ℝ → ℝ) (K : Fin n → ℝ) (η : ℝ) :
    ℝ → (Fin n → ℝ) → (Fin n → ℝ) :=
  fun t v => jordanBlock n *ᵥ v +
    (d t + b t * (-(K ⬝ᵥ (dil n (η * lam T a t) *ᵥ v)))) • eN n

end ChitourPrescribedTime.Linear


