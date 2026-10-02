-- Prove2me | Definitions.Def_ServiceParts_Palm_ResupplySystem
-- name    : ServiceParts_Palm_ResupplySystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T22:04:12.364264+00:00
-- url     : https://prove2.me/theorems/31ea1313-5f95-4de9-b185-48a3d65decec
-- title:
--   (s–1, s) backorder system: Poisson order stream with i.i.d. resupply times independent of arrivals
-- statement:
--   A single item is managed with an $(s-1,s)$ policy and backorders: every customer order asks for one unit and immediately triggers a resupply order, so the inventory position stays at the stock level $s$. The system is described by
--
--   1. the **order arrival rate** $\lambda > 0$;
--   2. **interarrival times** $A_0, A_1, \dots$ that are independent and exponentially distributed with rate $\lambda$, so the orders form a Poisson process with rate $\lambda$ started empty at time $0$; the $k$-th order (counted from $k = 0$) is placed at
--   $$T_k = A_0 + A_1 + \cdots + A_k;$$
--   3. **resupply times** $L_0, L_1, \dots$, where $L_k$ is the resupply time of the $k$-th order. They are nonnegative, identically distributed with a density $g$, distribution function $G(u) = P[L \le u]$ and finite mean $\bar\tau = E[L]$.
--
--   The whole family $A_0, A_1, \dots, L_0, L_1, \dots$ is mutually independent; in particular the resupply times are independent of the arrival process.
--
--   Derived quantities:
--
--   - $N(t) = \#\{k : T_k \le t\}$, the number of orders placed in $[0,t]$;
--   - $X(t) = \#\{k : T_k \le t < T_k + L_k\}$, the number of units in resupply at time $t$;
--   - $G(u)$ and $\bar\tau = E[L_0] = \int_0^\infty [1 - G(u)]\,du$.
--
--   This is the model of Theorem 6 (Palm's theorem) and of every backorder result of Section 3.1.
--
--   **Formalization Note** The stock level $s$ is not a field: in the backorder case the number of units in resupply does not depend on it. Independence of resupply times from the arrival stream is not written in Theorem 6 but is used on p. 40 ("the probability that the corresponding unit remains in the resupply system at time $t$ is $1 - G(t-s)$"), so it is part of the model. The counts $N(t)$ and $X(t)$ are defined as cardinalities of sets of order indices; on the probability-zero event where infinitely many orders fall in $[0,t]$ the cardinality convention returns $0$, which does not affect any probability.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 37-40, Chapter 3 introduction and Section 3.1.1 (hypotheses of Theorem 6, p. 39)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ServiceParts.Palm

/-- The backorder (s–1, s) resupply system of Muckstadt (2005), Section 3.1, pp. 37–40.
Customer orders arrive as a Poisson process with rate `rate` = λ, realised through i.i.d.
exponential interarrival times `gap k` (the `k`-th order, counted from `0`, is placed at time
`gap 0 + ⋯ + gap k`); each order immediately triggers a resupply order whose resupply time is
`resupply k`. Resupply times are i.i.d., nonnegative, have a density and a finite mean, and the
whole family of interarrival and resupply times is mutually independent (so resupply times are
independent of the arrival process). The system is empty at time `0`. The stock level `s` is not
part of the model: in the backorder case the number of units in resupply does not depend on it. -/
structure ResupplySystem (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) where
  /-- the customer order arrival rate λ -/
  rate : ℝ
  /-- interarrival times of the Poisson order stream -/
  gap : ℕ → Ω → ℝ
  /-- resupply time of the `k`-th order -/
  resupply : ℕ → Ω → ℝ
  /-- the common density `g` of the resupply times -/
  density : ℝ → ENNReal
  rate_pos : 0 < rate
  gap_measurable : ∀ k, Measurable (gap k)
  resupply_measurable : ∀ k, Measurable (resupply k)
  density_measurable : Measurable density
  /-- interarrival times are exponential with rate λ (Poisson order process) -/
  gap_law : ∀ k, P.map (gap k) = expMeasure rate
  /-- every resupply time has density `g` -/
  resupply_law : ∀ k, P.map (resupply k) = volume.withDensity density
  /-- resupply times are nonnegative -/
  resupply_nonneg : ∀ k ω, 0 ≤ resupply k ω
  /-- the mean resupply time τ̄ is finite -/
  resupply_integrable : Integrable (resupply 0) P
  /-- all interarrival and resupply times are mutually independent -/
  indep : iIndepFun (Sum.elim gap resupply) P

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The epoch `T_k = gap 0 + ⋯ + gap k` at which the `k`-th customer order (counted from `0`)
is placed. -/
noncomputable def ResupplySystem.arrival (S : ResupplySystem Ω P) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), S.gap i ω

/-- `N(t)`: the number of customer orders placed in `[0, t]` (`0` on the null event where
infinitely many orders fall in `[0, t]`). -/
noncomputable def ResupplySystem.orderCount (S : ResupplySystem Ω P) (t : ℝ) (ω : Ω) : ℕ :=
  {k : ℕ | S.arrival k ω ≤ t}.ncard

/-- `X(t)`: the number of units in resupply at time `t`, i.e. the number of orders placed by
time `t` whose resupply is not complete at time `t` (`T_k ≤ t < T_k + L_k`). -/
noncomputable def ResupplySystem.unitsInResupply (S : ResupplySystem Ω P) (t : ℝ) (ω : Ω) : ℕ :=
  {k : ℕ | S.arrival k ω ≤ t ∧ t < S.arrival k ω + S.resupply k ω}.ncard

/-- The resupply-time distribution function `G(u) = P[L ≤ u]`. -/
noncomputable def ResupplySystem.resupplyCdf (S : ResupplySystem Ω P) (u : ℝ) : ℝ :=
  (P {ω | S.resupply 0 ω ≤ u}).toReal

/-- The mean resupply time `τ̄ = E[L]`. -/
noncomputable def ResupplySystem.meanResupply (S : ResupplySystem Ω P) : ℝ :=
  ∫ ω, S.resupply 0 ω ∂P

end ServiceParts.Palm


