-- Prove2me | Definitions.Def_ServiceParts_NonstatPalm_CompoundResupplySystem
-- name    : ServiceParts_NonstatPalm_CompoundResupplySystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T07:40:39.473299+00:00
-- url     : https://prove2.me/theorems/9ad75088-9800-45bd-9cca-5b1d4350243a
-- title:
--   Single-location resupply system with nonstationary compound Poisson demand
-- statement:
--   The model of Section 9.2: orders arrive as a nonstationary Poisson process and each order is for a random number of units.
--
--   1. **Orders and resupply times.** Exactly as in the single-unit model: an order rate $\lambda(s) \ge 0$, integrable on bounded intervals, with $m(t) = \int_0^t \lambda(s)\,ds$; order epochs $T_k = \inf\{s \ge 0 : m(s) \ge \Gamma_k\}$ where $\Gamma_k$ are the points of a unit-rate Poisson process; marks $U_k$ with law $\nu$ and resupply times $\rho(T_k, U_k) \ge 0$, finite in mean, with $G_s(w) = \nu\{e : \rho(s,e) \le w\}$.
--   2. **Order sizes.** The $k$-th order is for $Q_k \ge 1$ units, with a time-stationary distribution $u_j = P(Q_k = j)$, $j \ge 1$ (so $u_0 = 0$).
--   3. **Shared resupply time.** All units of an order are resupplied together, at time $T_k + \rho(T_k, U_k)$.
--   4. **Independence.** The triples $(A_k, U_k, Q_k)$ are mutually independent across $k$, and within each triple the three components are independent.
--
--   Derived quantities: the number of orders $N(t)$ in $[0,t]$; the number of units demanded in $[0,t]$,
--   $$Y(t) = \sum_{k : \Gamma_k \le m(t)} Q_k;$$
--   the number of units in resupply at time $t$,
--   $$X(t) = \sum_{k : \Gamma_k \le m(t),\ t < T_k + \rho(T_k,U_k)} Q_k;$$
--   $G_s(w)$ and $\alpha(t) = \int_0^t (1 - G_s(t-s))\lambda(s)\,ds$; and the $n$-fold convolution $u^{(n)}_k$ of the order-size distribution ($u^{(0)}$ is the point mass at $0$, $u^{(n+1)}_k = \sum_{j=0}^k u_j\, u^{(n)}_{k-j}$), the probability that $n$ orders total $k$ units.
--
--   This is the model of the compound moment formulas and of Theorem 14.
--
--   **Formalization Note** Independence of order sizes from the order epochs and from the resupply times is not written in Section 9.2 but is used by the proof of Theorem 14 ("the number of orders in resupply at time $t$ has a Poisson distribution" and is then compounded). The single-unit model is repeated rather than extended so that each structure reads on its own. Sums over index sets are finite almost surely; on the null event where they are not, the convention returns $0$.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 217-218, Section 9.2 (model of Theorem 14)

import Mathlib
import Definitions.Def_ServiceParts_Palm_CompoundResupplySystem

open MeasureTheory ProbabilityTheory

namespace ServiceParts.NonstatPalm

/-- The single-location system of Muckstadt (2005), Section 9.2, pp. 217–218: nonstationary
Poisson *orders* with time-dependent resupply times, each order for a random number of units.
This structure repeats the model of Section 9.1 (rate λ, unit-rate points time-changed by
`m(t) = ∫₀ᵗ λ`, marks determining resupply times) and adds order sizes:

* `size k` is the number of units in the `k`-th order; the sizes have the time-stationary
  law `sizeLaw` on `{1, 2, …}` (`u_j = P(Q = j)`, `u_0 = 0`);
* all units of an order share the order's resupply time `resupply(T_k, mark k)`;
* the triples `((gap k, mark k), size k)` are independent across `k`, and within a triple the
  three components are independent (the triple's law is the product law). -/
structure CompoundResupplySystem (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
    (E : Type*) [MeasurableSpace E] where
  /-- the order rate λ(t) -/
  rate : ℝ → ℝ
  rate_nonneg : ∀ s, 0 ≤ rate s
  rate_intervalIntegrable : ∀ t, IntervalIntegrable rate volume 0 t
  /-- interarrival times of the underlying unit-rate Poisson process -/
  gap : ℕ → Ω → ℝ
  /-- the random mark of the `k`-th order, which determines its resupply time -/
  mark : ℕ → Ω → E
  markLaw : Measure E
  markLaw_isProb : IsProbabilityMeasure markLaw
  /-- `resupply s e`: the resupply time of an order placed at time `s` with mark `e` -/
  resupply : ℝ → E → ℝ
  resupply_measurable : Measurable (Function.uncurry resupply)
  resupply_nonneg : ∀ s e, 0 ≤ resupply s e
  resupply_integrable : ∀ s, 0 ≤ s → Integrable (resupply s) markLaw
  /-- the number of units in the `k`-th order -/
  size : ℕ → Ω → ℕ
  /-- the order-size distribution `u_j` -/
  sizeLaw : PMF ℕ
  /-- every order is for at least one unit -/
  sizeLaw_zero : sizeLaw 0 = 0
  gap_measurable : ∀ k, Measurable (gap k)
  mark_measurable : ∀ k, Measurable (mark k)
  size_measurable : ∀ k, Measurable (size k)
  /-- the gap is exponential(1), the mark has law `markLaw`, the size has law `sizeLaw`, and the
  three are independent -/
  triple_law : ∀ k, P.map (fun ω => ((gap k ω, mark k ω), size k ω)) =
    ((expMeasure 1).prod markLaw).prod sizeLaw.toMeasure
  /-- the triples are mutually independent across `k` -/
  triple_indep : iIndepFun (fun k ω => ((gap k ω, mark k ω), size k ω)) P

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : Type*} [MeasurableSpace E]

/-- `m(t) = ∫₀ᵗ λ(s) ds`. -/
noncomputable def CompoundResupplySystem.meanFn (S : CompoundResupplySystem Ω P E) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, S.rate s

/-- `Γ_k = gap 0 + ⋯ + gap k`. -/
noncomputable def CompoundResupplySystem.unitPoint (S : CompoundResupplySystem Ω P E) (k : ℕ)
    (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), S.gap i ω

/-- The epoch `T_k = inf {s ≥ 0 : m(s) ≥ Γ_k}` of the `k`-th order. -/
noncomputable def CompoundResupplySystem.epoch (S : CompoundResupplySystem Ω P E) (k : ℕ)
    (ω : Ω) : ℝ :=
  sInf {s : ℝ | 0 ≤ s ∧ S.unitPoint k ω ≤ S.meanFn s}

/-- The resupply time `resupply(T_k, mark_k)` shared by all units of the `k`-th order. -/
noncomputable def CompoundResupplySystem.resupplyTime (S : CompoundResupplySystem Ω P E) (k : ℕ)
    (ω : Ω) : ℝ :=
  S.resupply (S.epoch k ω) (S.mark k ω)

/-- `N(t)`: the number of orders in `[0, t]`. -/
noncomputable def CompoundResupplySystem.orderCount (S : CompoundResupplySystem Ω P E) (t : ℝ)
    (ω : Ω) : ℕ :=
  {k : ℕ | S.unitPoint k ω ≤ S.meanFn t}.ncard

/-- `Y(t)`: the number of units demanded in `[0, t]`, the total size of the orders in `[0, t]`. -/
noncomputable def CompoundResupplySystem.unitsDemanded (S : CompoundResupplySystem Ω P E) (t : ℝ)
    (ω : Ω) : ℕ :=
  ∑ᶠ (k : ℕ) (_ : S.unitPoint k ω ≤ S.meanFn t), S.size k ω

/-- `X(t)`: the number of units in resupply at time `t`, the total size of the orders placed in
`[0, t]` whose resupply is not complete at time `t`. -/
noncomputable def CompoundResupplySystem.unitsInResupply (S : CompoundResupplySystem Ω P E)
    (t : ℝ) (ω : Ω) : ℕ :=
  ∑ᶠ (k : ℕ) (_ : S.unitPoint k ω ≤ S.meanFn t ∧ t < S.epoch k ω + S.resupplyTime k ω),
    S.size k ω

/-- `G_s(w)`: the probability that an order placed at time `s` is resupplied within `w`. -/
noncomputable def CompoundResupplySystem.resupplyCdf (S : CompoundResupplySystem Ω P E)
    (s w : ℝ) : ℝ :=
  (S.markLaw {e | S.resupply s e ≤ w}).toReal

/-- `α(t) = ∫₀ᵗ (1 − G_s(t − s)) λ(s) ds`. -/
noncomputable def CompoundResupplySystem.alpha (S : CompoundResupplySystem Ω P E) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, (1 - S.resupplyCdf s (t - s)) * S.rate s

/-- The order-size probabilities `u_j` as real numbers. -/
noncomputable def CompoundResupplySystem.sizeProb (S : CompoundResupplySystem Ω P E) (j : ℕ) : ℝ :=
  (S.sizeLaw j).toReal

end ServiceParts.NonstatPalm


