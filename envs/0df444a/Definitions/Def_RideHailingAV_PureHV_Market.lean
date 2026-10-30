-- Prove2me | Definitions.Def_RideHailingAV_PureHV_Market
-- name    : RideHailingAV_PureHV_Market
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:49:54.319788+00:00
-- url     : https://prove2.me/theorems/89e6cb6b-57bb-4226-b118-704d9b7f402b
-- title:
--   Model constants of a pure-HV ride-hailing market
-- statement:
--   A pure-HV ride-hailing market is described by six real constants:
--
--   1. $a$ and $r$, the parameters of the **ETA function** $t_1(s)=a s^{-r}$, the average pickup time when $s$ cars are open, with ETA elasticity $0\le r<1$;
--   2. $t_2$, the average trip time;
--   3. $V$, the maximum rider value: riders' values for a ride-hour are uniform on $[0,V]$;
--   4. $w_0$ and $\alpha$, the HV supply curve $w(n_{HV})=w_0+\alpha n_{HV}$ with $\alpha\ge 0$: for a fleet of $n_{HV}$ human drivers to participate, their hourly earnings must be $w(n_{HV})$.
--
--   The potential demand mass $m_i$ of a scenario is a separate parameter of the objects built on these constants.
--
--   **Formalization Note** The structure carries the constants only. The paper's conditions on them ($0\le r<1$, $\alpha\ge 0$, positivity) are hypotheses of each theorem that needs them.
-- source:
--   Lian, van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), §3.1, eq. (1), p. 7; eq. (4) and the Market paragraph, p. 8

import Mathlib

namespace RideHailingAV.PureHV

/-- **The model constants of a pure-HV ride-hailing market.**
Lian, van Ryzin, *Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of
Market Configuration*, SSRN 3716491 (version of 23 August 2023), §3.1, pp. 7–9.

* `a`, `r`: the ETA function `t₁(s) = a s^(−r)`, `0 ≤ r < 1` (eq. (4), p. 8); `r` is the
  ETA elasticity.
* `t2`: the average trip time `t₂` (pp. 8–9).
* `V`: riders' values are uniform on `[0, V]` (p. 8).
* `w0`, `α`: the HV supply curve `w(n_HV) = w₀ + α n_HV`, `α ≥ 0` (eq. (1), p. 7).

**Formalization Note.** The structure carries the constants only; the paper's conditions on
them (`0 ≤ r < 1`, `α ≥ 0`, positivity) are hypotheses of each theorem that needs them. -/
structure Market where
  /-- ETA scale `a` in `t₁(s) = a s^(−r)`, eq. (4). -/
  a : ℝ
  /-- ETA elasticity `r` in `t₁(s) = a s^(−r)`, eq. (4). -/
  r : ℝ
  /-- Average trip time `t₂`. -/
  t2 : ℝ
  /-- Maximum rider value `V`. -/
  V : ℝ
  /-- Base reservation earnings `w₀`, eq. (1). -/
  w0 : ℝ
  /-- Slope `α` of the HV supply curve, eq. (1). -/
  α : ℝ

end RideHailingAV.PureHV


