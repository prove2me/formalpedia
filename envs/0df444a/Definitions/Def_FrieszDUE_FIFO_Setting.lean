-- Prove2me | Definitions.Def_FrieszDUE_FIFO_Setting
-- name    : FrieszDUE_FIFO_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:07:24.777981+00:00
-- url     : https://prove2.me/theorems/7691bfb4-e46a-409a-ac89-be66fe75a41f
-- title:
--   §3, p. 185 — linear arc delay (18), arc volume x(t), exit-time equation τ(t) = t + D(t), partition times tₙ
-- statement:
--   This file fixes the single-arc model of §3 of Friesz et al. (1993). Vehicles enter one arc of a traffic network at the **entry rate** $u(t)$ (vehicles per unit time); the first vehicle enters at time $0$. A vehicle entering at time $t$ leaves the arc at its **exit time** $\tau(t)$.
--
--   1. **Linear delay (18).** For constants $\alpha, \beta$ the delay of a vehicle entering an arc that holds volume $x$ is
--   $$D(x) = \alpha x + \beta .$$
--   2. **Arc volume.** Given $u$ and $\tau$, the volume on the arc at time $t \ge 0$ is the inflow mass of the vehicles that entered during $[0, t]$ and have not yet exited at time $t$:
--   $$x(t) = \int_{\{s \in [0,t]\,:\, \tau(s) > t\}} u(s)\, ds .$$
--   A vehicle whose exit time equals $t$ has already left.
--   3. **Exit-time equation.** $\tau$ is the exit-time function produced by the linear delay under the entry rate $u$ when, for every $t \ge 0$,
--   $$\tau(t) = t + D(t), \qquad D(t) = \alpha\, x(t) + \beta .$$
--   4. **Partition times.** $t_0 = 0$ and $t_{n+1} = \tau(t_n)$; in particular $t_1 = \tau(0)$ is the exit time of the first vehicle.
--
--   The exit-time equation is implicit: $\tau$ appears on both sides, through the volume. It is the object of Theorem 1, which asserts that every such $\tau$ is strictly increasing.
--
--   **Formalization Note** The paper writes the volume as $\int_{\tau^{-1}(t)}^{t} u(s)\,ds$, which presupposes the invertibility of $\tau$ that Theorem 1 proves. Here the volume is defined directly as the mass of the vehicles that are on the arc at time $t$, so no monotonicity or invertibility of $\tau$ is built into the model. The equation constrains $\tau$ only at entry times $t \ge 0$. Integrals are with respect to Lebesgue measure.
-- source:
--   Friesz, Bernstein, Smith, Tobin and Wie, A variational inequality formulation of the dynamic network user equilibrium problem, Oper. Res. 41 (1993), p. 185, §3, (18), the single-arc notation τ(t) = t + D(t), and the proof of Theorem 1 ((21), (25), (32), x(0) = 0)

import Mathlib

namespace FrieszDUE.FIFO

/-- The linear arc delay function (18): `D(x) = α x + β`, the delay of a vehicle entering an
arc that holds volume `x`. -/
def linearDelay (α β x : ℝ) : ℝ := α * x + β

/-- The arc volume `x(t)` at time `t ≥ 0` for entry rate `u` and exit-time function `τ`: the
inflow mass of the vehicles that entered the arc during `[0, t]` (the first vehicle enters at
time `0`) and have not exited by time `t`, i.e. whose exit time `τ s` is strictly later than
`t`. -/
noncomputable def arcVolume (u τ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in {s : ℝ | s ∈ Set.Icc 0 t ∧ t < τ s}, u s

/-- `τ` is the arc exit-time function produced by the linear delay (18) under the entry rate
`u`: for every entry time `t ≥ 0`, `τ(t) = t + D(t)` with `D(t) = α x(t) + β`, where `x(t)`
is the arc volume `arcVolume u τ t`. -/
def IsLinearExitTime (α β : ℝ) (u τ : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → τ t = t + linearDelay α β (arcVolume u τ t)

/-- The partition times of the proof of Theorem 1: `t₀ = 0` and `t_{n+1} = τ(t_n)`, so that
`t₁ = τ(0)` is the exit time of the first vehicle. -/
def tSeq (τ : ℝ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => τ (tSeq τ n)

end FrieszDUE.FIFO


