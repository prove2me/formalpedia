-- Prove2me | Definitions.Def_ReedGGN_Regulator_Equation
-- name    : ReedGGN_Regulator_Equation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:27.333686+00:00
-- url     : https://prove2.me/theorems/aad57e63-8e8b-4011-accf-af19f9f2a25a
-- title:
--   Equation (3.1) z(t) = x(t) + ∫₀ᵗ (z(t−s)+a)⁺ dB(s), the operator Ψᵃ_B, and the successive approximations (A.3)
-- statement:
--   Let $B$ be a cumulative distribution function on $\mathbb R$, represented by its law $\mu$ (a probability measure on $\mathbb R$ with $B(t)=\mu((-\infty,t])$), and let $a\in\mathbb R$.
--
--   1. For a path $u$, the operator of the proof of Proposition 3.1 (p. 34) is
--   $$\Psi^a_B(u)(t)=\int_{[0,t]}\big(u(t-s)+a\big)^+\,dB(s),\qquad t\ge 0,$$
--   where $y^+=\max(y,0)$.
--   2. A path $z$ **solves the regulator equation (3.1)** with input $x$ if
--   $$z(t)=x(t)+\int_{[0,t]}\big(z(t-s)+a\big)^+\,dB(s)\qquad\text{for every } t\ge 0.$$
--   3. The **successive approximations (A.3)** with input $x$ are $u_0\equiv 0$ and $u_{n+1}(t)=x(t)+\Psi^a_B(u_n)(t)$ for $n\ge 0$.
--
--   Equation (3.1) is the regulator equation of §3: with $B=F$ the service-time distribution and $a=-1$ (fluid scale) or $a=0$ (diffusion scale) it represents the queue length of the $G/GI/N$ queue in the Halfin–Whitt regime.
--
--   **Formalization Note** The Stieltjes integral $\int_0^t\cdots dB(s)$ is the Lebesgue integral over the **closed** interval $[0,t]$ with respect to $\mu$, so an atom of $B$ at $0$ is included, as the paper states on p. 37. For $t<0$ the interval is empty and $\Psi^a_B(u)(t)=0$. The integral is Lean's Bochner integral, which is $0$ for a non-integrable integrand; every statement of the mission applies (3.1) only to càdlàg paths, for which the integrand is bounded and measurable on $[0,t]$, so the integral is the true one. The paper writes (A.3) "for $n\ge1$"; the recursion starts at $n=0$.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, p. 9, Eq. (3.1); p. 32, Eq. (A.3); p. 34, definition of Ψᵃ_B; p. 37 (closed intervals [0, t])

import Mathlib

namespace ReedGGN.Regulator

open MeasureTheory

/-- The operator `Ψ^a_B` of the proof of Proposition 3.1 (p. 34):
`Ψ^a_B(u)(t) = ∫_0^t (u(t − s) + a)^+ dB(s)`. The cumulative distribution function `B` on `ℝ`
is represented by its law `μ` (so `B(t) = μ((−∞, t])`), and the Stieltjes integral is over
the closed interval `[0, t]`, an atom of `B` at `0` included (Appendix, p. 37). For `t < 0`
the interval is empty and the value is `0`. -/
noncomputable def psi (μ : Measure ℝ) (a : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in Set.Icc 0 t, max (u (t - s) + a) 0 ∂μ

/-- `z` solves the regulator equation (3.1) (p. 9) with input `x`:
`z(t) = x(t) + ∫_0^t (z(t − s) + a)^+ dB(s)` for every `t ≥ 0`, with `B` the distribution
function of `μ` and the integral over the closed interval `[0, t]`. -/
def SolvesRegulator (μ : Measure ℝ) (a : ℝ) (x z : ℝ → ℝ) : Prop :=
  ∀ t, 0 ≤ t → z t = x t + ∫ s in Set.Icc 0 t, max (z (t - s) + a) 0 ∂μ

/-- The successive approximations (A.3) (p. 32): `u_0 = 0` and
`u_{n+1}(t) = x(t) + ∫_0^t (u_n(t − s) + a)^+ dB(s)`. -/
noncomputable def picard (μ : Measure ℝ) (a : ℝ) (x : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun t => x t + psi μ a (picard μ a x n) t

end ReedGGN.Regulator


