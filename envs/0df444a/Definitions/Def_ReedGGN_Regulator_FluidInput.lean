-- Prove2me | Definitions.Def_ReedGGN_Regulator_FluidInput
-- name    : ReedGGN_Regulator_FluidInput
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:29.936978+00:00
-- url     : https://prove2.me/theorems/c9736eeb-3c9f-4dbc-b623-9b5dc806f858
-- title:
--   The service tail G, the equilibrium distribution F_e (5.4), and the input terms of the fluid equation (4.7) with Ā = e
-- statement:
--   Let $\mu$ be the law of a service time and $F(t)=\mu((-\infty,t])$ its distribution function.
--
--   1. The **tail** is $G(t)=1-F(t)=\mu((t,\infty))$.
--   2. The **equilibrium distribution** (5.4) is
--   $$F_e(x)=\int_0^x G(u)\,du,\qquad x\ge 0.$$
--   3. For an initial fluid content $\bar Q_0\in\mathbb R$, an initial residual-service tail $\bar F_0=1-F_0$, and the fluid arrival process $\bar A=e$, $e(t)=t$, the **input of the fluid equation (4.7)** is
--   $$x(t)=\min(\bar Q_0,1)\,\bar F_0(t)+(\bar Q_0-1)^+G(t)+\int_0^t G(t-s)\,ds .$$
--
--   With this input, (4.7) reads $\bar Q(t)=x(t)+\int_0^t(\bar Q(t-s)-1)^+\,dF(s)$, which is the regulator equation (3.1) with $B=F$ and $a=-1$. This is how Example 1 and the proof of Corollary 5.1 use (4.7).
--
--   **Formalization Note** $\int_0^t G(t-s)\,d\bar A(s)$ with $\bar A=e$ is the Lebesgue integral of $s\mapsto G(t-s)$ over $[0,t]$. $F_e(x)$ for $x<0$ is $0$ (empty interval); the paper defines it only for $x\ge 0$. The tail $\bar F_0$ is passed as a function, so that both a law ($F_0=F$ in Example 1) and $F_e$ ($F_0=F_e$ in Corollary 5.1, $\bar F_0=1-F_e$) can be used.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, p. 6 (G = 1 − F); p. 12, Eq. (4.7); p. 18, Eq. (5.4)

import Mathlib

namespace ReedGGN.Regulator

open MeasureTheory

/-- The tail `G(t) = 1 − F(t) = μ((t, ∞))` of the law `μ` of a service time (p. 6). -/
noncomputable def tail (μ : Measure ℝ) (t : ℝ) : ℝ :=
  (μ (Set.Ioi t)).toReal

/-- The equilibrium distribution (5.4) (p. 18): `F_e(x) = ∫_0^x G(u) du` (Lebesgue measure),
for `x ≥ 0`; for `x < 0` the integral is over the empty set and the value is `0`. -/
noncomputable def Fe (μ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ u in Set.Icc 0 x, tail μ u

/-- The first three terms of the fluid equation (4.7) (p. 12) when the fluid arrival process is
`Ā = e`, the identity `e(t) = t` (so `dĀ(s) = ds`):
`min(Q̄₀, 1) F̄₀(t) + (Q̄₀ − 1)^+ G(t) + ∫_0^t G(t − s) ds`.
Here `Q0` is `Q̄₀`, `F0bar` is the tail `F̄₀ = 1 − F₀` of the initial residual service law, and
`G` is the tail of the service law `μ`. -/
noncomputable def fluidInput (Q0 : ℝ) (F0bar : ℝ → ℝ) (μ : Measure ℝ) (t : ℝ) : ℝ :=
  min Q0 1 * F0bar t + max (Q0 - 1) 0 * tail μ t + ∫ s in Set.Icc 0 t, tail μ (t - s)

end ReedGGN.Regulator


