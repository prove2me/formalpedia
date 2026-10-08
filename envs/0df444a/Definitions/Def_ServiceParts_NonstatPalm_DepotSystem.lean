-- Prove2me | Definitions.Def_ServiceParts_NonstatPalm_DepotSystem
-- name    : ServiceParts_NonstatPalm_DepotSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T07:40:34.490912+00:00
-- url     : https://prove2.me/theorems/04aa0620-1342-4d98-89f6-caa3ef94d492
-- title:
--   Two-echelon depot repair system with nonstationary Poisson failures and deterministic, noncrossing depot repair times
-- statement:
--   The depot side of the two-echelon (depot and bases) system of Section 9.3, for one item and $n_b$ bases $i = 1, \dots, n_b$.
--
--   1. **Failures at base $i$** form a nonstationary Poisson process with rate $\lambda_i(s) \ge 0$, integrable on bounded intervals, and mean function $m_i(t) = \int_0^t \lambda_i(s)\,ds$ (built, as in Section 9.1, by time-changing a unit-rate Poisson process: $T_{i,k} = \inf\{s \ge 0 : m_i(s) \ge \Gamma_{i,k}\}$).
--   2. **Repair location.** Each failure at base $i$ is repaired at the base with probability $r_i \in [0,1]$ and sent to the depot with probability $1 - r_i$.
--   3. **Depot repair cycle.** A failure entering depot repair at time $u$ leaves it at time $u + D(u)$, where the depot repair cycle time $D(u) \ge 0$ is deterministic and time-dependent, and satisfies the no-crossing condition
--   $$D(t) + t \ge D(s) + s \qquad (s < t).$$
--   4. **Independence.** All interarrival times of the unit-rate processes and all repair-location indicators, over all bases and failures, are mutually independent.
--
--   Derived quantities: the number of units in the depot resupply (repair) system at time $t$,
--   $$X_0(t) = \sum_i \#\{k : T_{i,k} \le t,\ \text{failure } (i,k) \text{ sent to the depot},\ t < T_{i,k} + D(T_{i,k})\};$$
--   the cutoff $\tilde t = \inf\{u \ge 0 : D(u) + u > t\}$; and
--   $$m_0(\tilde t, t) = \int_{\tilde t}^{t} \sum_i \lambda_i(u)(1 - r_i)\,du.$$
--
--   **Formalization Note** Base stock levels, depot stock levels, order-and-ship times $A_i$ and base repair times $E_i$ of Section 9.3.1 are not fields: the number of units in depot repair does not depend on them. The book writes $\tilde t = \inf\{u : D(u) + u > t\}$ with time implicitly nonnegative; the infimum is taken over $u \ge 0$, where the set is nonempty (it contains every $u > t$) and bounded below. $D \ge 0$ (a repair cycle time) is implicit in the book.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 218-221, Sections 9.3, 9.3.1, 9.3.2

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ServiceParts.NonstatPalm

/-- The depot side of the two-echelon system of Muckstadt (2005), Section 9.3, pp. 218–221,
for a single item and `nb` bases (indexed by `Fin nb`).

* Failures (demands) at base `i` form a nonstationary Poisson process with rate `rate i` = λᵢ
  (λᵢ ≥ 0, integrable on bounded intervals), constructed as a unit-rate Poisson process with
  exponential(1) gaps `gap i k`, time-changed by `mᵢ(t) = ∫₀ᵗ λᵢ(s) ds`.
* The `k`-th failure at base `i` is sent to the depot for repair when `toDepot i k = true`,
  which has probability `1 − rᵢ`; with probability `rᵢ` it is repaired at the base.
* A failure entering depot repair at time `u` completes its depot repair cycle at time
  `u + D(u)`, where the depot repair cycle time `D(u) ≥ 0` is deterministic and time-dependent
  and satisfies the no-crossing condition `D(t) + t ≥ D(s) + s` for `s < t`.
* All gaps and routing indicators, over all bases and all failures, are mutually independent. -/
structure DepotSystem (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (nb : ℕ) where
  /-- the failure rate λᵢ(t) at base `i` -/
  rate : Fin nb → ℝ → ℝ
  rate_nonneg : ∀ i s, 0 ≤ rate i s
  rate_intervalIntegrable : ∀ i t, IntervalIntegrable (rate i) volume 0 t
  /-- `rᵢ`: the probability that a failure at base `i` is repaired at the base -/
  baseRepairProb : Fin nb → ℝ
  baseRepairProb_mem : ∀ i, baseRepairProb i ∈ Set.Icc (0 : ℝ) 1
  /-- `D(t)`: the deterministic depot repair cycle time for a failure occurring at time `t` -/
  depotCycle : ℝ → ℝ
  depotCycle_nonneg : ∀ t, 0 ≤ depotCycle t
  /-- no crossing: `D(t) + t ≥ D(s) + s` for `s < t` -/
  depotCycle_noCrossing : ∀ s t, s < t → depotCycle s + s ≤ depotCycle t + t
  /-- interarrival times of the unit-rate process underlying base `i`'s failures -/
  gap : Fin nb → ℕ → Ω → ℝ
  /-- whether the `k`-th failure at base `i` is repaired at the depot -/
  toDepot : Fin nb → ℕ → Ω → Bool
  gap_measurable : ∀ i k, Measurable (gap i k)
  toDepot_measurable : ∀ i k, Measurable (toDepot i k)
  gap_law : ∀ i k, P.map (gap i k) = expMeasure 1
  toDepot_prob : ∀ i k, P {ω | toDepot i k ω = true} = ENNReal.ofReal (1 - baseRepairProb i)
  /-- all gaps and routing indicators are mutually independent -/
  indep : iIndepFun (Sum.elim (fun p : Fin nb × ℕ => gap p.1 p.2)
    (fun p : Fin nb × ℕ => fun ω => if toDepot p.1 p.2 ω then (1 : ℝ) else 0)) P

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {nb : ℕ}

/-- `mᵢ(t) = ∫₀ᵗ λᵢ(s) ds`. -/
noncomputable def DepotSystem.meanFn (S : DepotSystem Ω P nb) (i : Fin nb) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, S.rate i s

/-- The `k`-th point `Γ_{i,k} = gap i 0 + ⋯ + gap i k` of base `i`'s unit-rate process. -/
noncomputable def DepotSystem.unitPoint (S : DepotSystem Ω P nb) (i : Fin nb) (k : ℕ)
    (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), S.gap i j ω

/-- The epoch `T_{i,k} = inf {s ≥ 0 : mᵢ(s) ≥ Γ_{i,k}}` of the `k`-th failure at base `i`. -/
noncomputable def DepotSystem.epoch (S : DepotSystem Ω P nb) (i : Fin nb) (k : ℕ) (ω : Ω) : ℝ :=
  sInf {s : ℝ | 0 ≤ s ∧ S.unitPoint i k ω ≤ S.meanFn i s}

/-- `X₀(t)`: the number of units in the depot resupply (repair) system at time `t`: failures at
any base, occurring in `[0, t]`, sent to the depot, whose depot repair cycle is not complete at
time `t` (`t < T + D(T)`). -/
noncomputable def DepotSystem.depotInResupply (S : DepotSystem Ω P nb) (t : ℝ) (ω : Ω) : ℕ :=
  ∑ i : Fin nb, {k : ℕ | S.unitPoint i k ω ≤ S.meanFn i t ∧ S.toDepot i k ω = true ∧
    t < S.epoch i k ω + S.depotCycle (S.epoch i k ω)}.ncard

/-- `t̃ = inf {u ≥ 0 : D(u) + u > t}`: every depot entry before `t̃` has left depot repair by
time `t`, every entry after `t̃` is still in it. -/
noncomputable def DepotSystem.cutoff (S : DepotSystem Ω P nb) (t : ℝ) : ℝ :=
  sInf {u : ℝ | 0 ≤ u ∧ t < S.depotCycle u + u}

/-- `m₀(t̃, t) = ∫_{t̃}^{t} Σᵢ λᵢ(u)(1 − rᵢ) du`. -/
noncomputable def DepotSystem.depotMean (S : DepotSystem Ω P nb) (t : ℝ) : ℝ :=
  ∫ u in S.cutoff t..t, ∑ i : Fin nb, S.rate i u * (1 - S.baseRepairProb i)

end ServiceParts.NonstatPalm


