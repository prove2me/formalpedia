-- Prove2me | Definitions.Def_ServiceParts_Shortfall_ShortfallModel
-- name    : ServiceParts_Shortfall_ShortfallModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T23:14:31.541375+00:00
-- url     : https://prove2.me/theorems/136a0019-63f2-4400-8083-ef7529b434ad
-- title:
--   Capacity-limited single-item system: i.i.d. demand, capacity c, shortfall recursion (8.1), stationary shortfall V
-- statement:
--   A single item is produced in every period $n = 1, 2, \dots$ of an infinite horizon at a facility that can produce at most $c$ units per period. The demand of period $n$ is a random variable $D_n$. The standing assumptions of Section 8.1 are:
--
--   1. the demands $D_1, D_2, \dots$ are nonnegative, independent and identically distributed, with the law of a generic demand $D$;
--   2. the expected demand is finite and strictly less than the capacity, $E[D] < c$.
--
--   Under the **modified $(s-1, s)$ policy** with target level $s$, the system starts with net inventory $I_0 = s$; in period $n$ the demand $D_n$ is observed and the production quantity is $\min\{c,\ s - I_{n-1} + D_n\}$, so the end-of-period net inventory is
--   $$I_n = I_{n-1} - D_n + \min\{c,\ s - I_{n-1} + D_n\}.$$
--   Negative net inventory is backordered demand.
--
--   The **shortfall process** is defined by $V_0 = 0$ and the recursion (8.1)
--   $$V_n = \left[V_{n-1} + D_n - c\right]^+, \qquad n \ge 1.$$
--
--   With the random walk $S_n = \sum_{k=1}^{n} (D_k - c)$, $S_0 = 0$, the **stationary shortfall** is
--   $$V = \sup_{n \ge 0} S_n \in [0, \infty].$$
--   Its law is the stationary distribution of the shortfall process referred to on p. 184 (this identification is the milestone "Section 8.1.1").
--
--   Finally, a probability law $\mu$ on $\mathbb R$ is called **lattice** if there are $a \in \mathbb R$ and $d > 0$ with $\mu(a + d\mathbb Z) = 1$; otherwise it is non-lattice.
--
--   These objects are shared by every statement of the mission about the continuous-demand case (Section 8.1.1, 8.1.3, Theorem 11).
--
--   **Formalization Note** Demand of period $n$ is `demand n` for $n \ge 1$; `demand 0` is one more i.i.d. copy that no statement uses. The supremum $V$ is taken in $[0, \infty]$ and then converted to a real number; the conversion gives $0$ only on the event $\{V = \infty\}$, which has probability zero under $E[D] < c$. The mean $E[D]$ is a Bochner integral, made meaningful by the integrability field.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 183-185, Section 8.1 and 8.1.1 (model, modified (s-1,s) policy, Eq. (8.1), V_0 = 0); p. 191 (Theorem 11)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ServiceParts.Shortfall

/-- The single-item capacity-limited production system of Muckstadt (2005), Section 8.1,
pp. 183–185. One item is produced in every period of an infinite horizon; at most `capacity` = c
units can be produced per period. The demand of period `n` (periods are numbered `n = 1, 2, …`
as in the book) is `demand n`; `demand 0` is one more independent copy that no statement uses.
Demands are nonnegative, independent and identically distributed, have a finite mean, and the
expected per-period demand is strictly less than the capacity (the standing assumption of
Section 8.1.1, p. 184). -/
structure ShortfallModel (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] where
  /-- the per-period production capacity `c` -/
  capacity : ℝ
  /-- `demand n` is the demand `D_n` of period `n` (for `n ≥ 1`) -/
  demand : ℕ → Ω → ℝ
  demand_measurable : ∀ n, Measurable (demand n)
  /-- demands are nonnegative -/
  demand_nonneg : ∀ n ω, 0 ≤ demand n ω
  /-- the demands of different periods are mutually independent -/
  demand_indep : iIndepFun demand P
  /-- the demands of all periods have the same law as `D_1` -/
  demand_identDistrib : ∀ n, IdentDistrib (demand n) (demand 1) P P
  /-- the expected per-period demand `E[D]` is finite -/
  demand_integrable : Integrable (demand 1) P
  /-- standing assumption of Section 8.1.1: `E[D] < c` -/
  mean_lt_capacity : ∫ ω, demand 1 ω ∂P < capacity

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- End-of-period net inventory `I_n` under the modified `(s–1, s)` policy with target level `s`
(p. 184): the system starts with net inventory `s` (no shortfall, `V_0 = 0`); in period `n` the
demand `D_n` is observed and the production quantity is `min {c, s − I_{n−1} + D_n}`, i.e. enough
to end the period with `s` units if capacity permits, and `c` units otherwise. Unsatisfied demand
is backordered (negative net inventory). -/
noncomputable def ShortfallModel.netInventory (M : ShortfallModel Ω P) (s : ℝ) :
    ℕ → Ω → ℝ
  | 0 => fun _ => s
  | n + 1 => fun ω =>
      M.netInventory s n ω - M.demand (n + 1) ω
        + min M.capacity (s - M.netInventory s n ω + M.demand (n + 1) ω)

/-- The shortfall process `V_n` of Section 8.1.1: `V_0 = 0` (p. 185) and the Lindley recursion
(8.1), `V_n = [V_{n−1} + D_n − c]^+`. -/
noncomputable def ShortfallModel.shortfall (M : ShortfallModel Ω P) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun ω => max (M.shortfall n ω + M.demand (n + 1) ω - M.capacity) 0

/-- The random walk `S_n = ∑_{k=1}^{n} (D_k − c)`, with `S_0 = 0`. -/
noncomputable def ShortfallModel.walk (M : ShortfallModel Ω P) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, (M.demand k ω - M.capacity)

/-- The all-time maximum `sup_{n ≥ 0} S_n ∈ [0, ∞]` of the random walk (nonnegative because
`S_0 = 0`), computed in the extended nonnegative reals so that no junk value arises. -/
noncomputable def ShortfallModel.walkMax (M : ShortfallModel Ω P) (ω : Ω) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (M.walk n ω)

/-- The stationary shortfall `V` of Section 8.1.1 ("a stationary distribution exists for the
shortfall process. Let V represent this random variable", p. 184), realised as the maximum of
the random walk, `V = sup_{n ≥ 0} ∑_{k=1}^{n} (D_k − c)`. Under `E[D] < c` the maximum is finite
almost surely; the conversion to a real number returns `0` only on the null event where it is
infinite. That its law is the limit law of `V_n` started from `V_0 = 0`, and a stationary law of
the recursion (8.1), is the milestone `stationary_shortfall_exists`. -/
noncomputable def ShortfallModel.stationaryShortfall (M : ShortfallModel Ω P) (ω : Ω) : ℝ :=
  (M.walkMax ω).toReal

/-- A law `μ` on `ℝ` is a **lattice** law when it is concentrated on an arithmetic progression
`a + dℤ` for some `a` and some span `d > 0`. Integer-valued demand is lattice; a law with a
density (or a nonzero absolutely continuous part) is not. -/
def IsLattice (μ : Measure ℝ) : Prop :=
  ∃ a d : ℝ, 0 < d ∧ μ {x : ℝ | ∃ k : ℤ, x = a + k * d}ᶜ = 0

end ServiceParts.Shortfall


