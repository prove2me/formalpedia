-- Prove2me | Definitions.Def_LostSalesRQ_model
-- name    : LostSalesRQ_model
-- status  : Definition
-- author  : @Ming Hu
-- created : 2026-11-17T18:23:18.045671+00:00
-- url     : https://prove2.me/theorems/150f740b-cfaf-4ae3-b919-b50984b8db3d
-- title:
--   Continuous-review lost-sales inventory system: demand environments, admissible policies, costs, $\mathrm{OPT}$ and the $(r,Q)$ family
-- statement:
--   Primitive data: demand rate $\lambda\ge0$ (unit Poisson demand), deterministic lead time $L\ge0$, holding cost rate $h\ge0$, lost-sales penalty $p\ge0$, fixed ordering cost $K\ge0$.
--
--   **Demand environments.** A demand environment $S$ is a probability space $(\Omega,\nu)$ with a filtration $(\mathcal F_t)_{t\in\mathbb R}$ and a cumulative demand count $N(t)$, the number of unit demands in $(0,t]$ ($N(t)=0$ for $t\le0$). $N$ is adapted, nondecreasing and right-continuous, and for $0\le s\le t$ the increment $N(t)-N(s)$ is Poisson with mean $\lambda(t-s)$ and independent of $\mathcal F_s$. The information $\mathcal F_t$ carries everything a policy may use: the demand history and independent private randomization.
--
--   **Admissible policies.** A policy on $S$ consists of a free initial supply, the number of units available by each time $t$ (on hand at $t=0$, then deliveries of an initial pipeline with no bound by $L$ on residual delivery times), which is finite and $\mathcal F_0$-measurable, and a cumulative order process $U(t)$, the number of units ordered in $[0,t]$. $U$ is adapted to $(\mathcal F_t)$ (so an order at a demand epoch may follow that demand), nondecreasing, integer-valued and right-continuous, hence it has finitely many order epochs on bounded intervals.
--
--   **Dynamics.** Units ordered at $t$ arrive at $t+L$. Demand epochs are processed in increasing order; at each epoch the arriving demands are served from the units delivered strictly before the epoch, net of demands already served, and the rest are lost. $X(t)$ is on-hand stock, $\mathcal A(t)$ and $\mathcal U(t)=N(t)-\mathcal A(t)$ the served and lost demands, and $O(T)$ the number of order epochs in $[0,T]$. The cost and the unrestricted optimum are
--   $$C(\pi)=\limsup_{T\to\infty}\frac1T\,\mathbb E\Big[h\int_0^TX(t)\,dt+p\,\mathcal U(T)+K\,O(T)\Big],\qquad \mathrm{OPT}=\inf_{S}\ \inf_{\pi\text{ on }S}C(\pi),$$
--   the infimum ranging over all demand environments of rate $\lambda$ and all admissible policies on them. $\mathrm{OPT}_k(\mu,a)$ is $\mathrm{OPT}$ at $\lambda=h=1$, $L=\mu$, $p=a$, $K=k$.
--
--   **Policy families.** The no-order policy starts empty and never orders. A policy follows the $(r,Q)$ rule if it starts with $r+Q$ units on hand and an empty pipeline and a served demand that lowers the inventory position from $r+1$ to $r$ triggers an immediate order of $Q$ units; equivalently $U(t)=Q\lfloor\mathcal A(t)/Q\rfloor$. $\Pi_{\rm rQ}$ collects these policies ($r\ge0$, $Q\ge1$) and the no-order policy; $\Pi_{\rm S}$ collects base stock $j\ge1$ (the $(j-1,1)$ rule) and the no-order policy. The selection rule of Corollary 1 takes the $(S^\star-1,Q_k)$ rule if $S^\star\ge1$ and $U_\mu(a)+b_k<a$, and the no-order policy otherwise. Expected holding, order count and served demand on $[0,T]$ are also defined, for Lemma J.1.
--
--   **Formalization Note** Expected costs, their upper limits and the infima are in $[0,\infty]$. Infinite expected cost stays infinite, and a zero cost coefficient times an infinite expectation is zero, which matches the paper's convention that finite expected cost is required only when the coefficient is positive. Simultaneous demands (a null event under the Poisson law) are served up to the available stock. The $(r,Q)$ rule is a predicate on policies; its existence on every demand environment is a milestone.
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Section 3 (pp. 6-7): Section 3.1 and eq. (3), Section 3.2, Section 3.3 and Table 2; Corollary 1 (p. 9); Lemma J.1 (p. A21).

import Definitions.Def_LostSalesRQ_poisson_functions
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.Finset.Sort

/-!
# The continuous-review lost-sales inventory system

Operational model of M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review
Lost-Sales Inventory Systems", Section 3: unit Poisson demand of rate `lam`, deterministic lead
time `L`, holding cost rate `h`, lost-sales penalty `p`, fixed ordering cost `K`.

A demand environment is a probability space with a filtration carrying the cumulative demand
count `N`, whose increments after any time `s ≥ 0` are Poisson and independent of the
information at `s`. The information carries everything a policy may use: the demand history and
independent private randomization. A policy is a free, finite initial supply (on hand at time
`0` or pending with arbitrary residual delivery times, chosen from the information at time `0`)
together with an adapted, nondecreasing, right-continuous cumulative order process. Orders arrive
`L` time units after they are placed. Demand is served from on-hand stock when it is positive and
is lost otherwise; units arriving at an epoch serve only later demand. Stock cannot be discarded
and orders cannot be cancelled.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace LostSalesRQ

/-- A demand environment for demand rate `lam` (Section 3.1). `N t` is the number of demands in
`(0, t]` (zero for `t ≤ 0`); it is adapted, nondecreasing and right-continuous, every increment
`N t - N s` with `0 ≤ s ≤ t` is Poisson with mean `lam (t - s)`, and is independent of the
information `𝓕 s` available at time `s`. -/
structure DemandSpace (lam : ℝ) where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  ν : Measure Ω
  [prob : IsProbabilityMeasure ν]
  𝓕 : Filtration ℝ mΩ
  N : ℝ → Ω → ℕ
  N_adapted : ∀ t, Measurable[𝓕 t] (N t)
  N_nonpos : ∀ ω t, t ≤ 0 → N t ω = 0
  N_mono : ∀ ω, Monotone (fun t => N t ω)
  N_rcont : ∀ ω t, ∃ δ > 0, ∀ s, t ≤ s → s < t + δ → N s ω = N t ω
  N_law : ∀ s t, 0 ≤ s → s ≤ t → ∀ k : ℕ,
    ν {ω | N t ω - N s ω = k} = ENNReal.ofReal (poisMass (lam * (t - s)) k)
  N_indep : ∀ s t, 0 ≤ s → s ≤ t →
    Indep (MeasurableSpace.comap (fun ω => N t ω - N s ω) inferInstance) (𝓕 s) ν

attribute [instance] DemandSpace.mΩ DemandSpace.prob

/-- An admissible replenishment policy on the demand environment `S` (Section 3.1).
`init t ω` is the number of free initial units available by time `t` (on hand at `t = 0`, then
deliveries of the initial pipeline, with no bound on their residual delivery times); it is
finite and determined by the information at time `0`. `U t ω` is the cumulative number of units
ordered in `[0, t]`; it is adapted (an order at time `t` may use the demand at `t`),
nondecreasing and right-continuous, hence has finitely many order epochs on bounded intervals. -/
structure Policy {lam : ℝ} (S : DemandSpace lam) where
  init : ℝ → S.Ω → ℕ
  U : ℝ → S.Ω → ℕ
  init_meas : ∀ t, Measurable[S.𝓕 0] (init t)
  init_nonpos : ∀ ω t, t < 0 → init t ω = 0
  init_mono : ∀ ω, Monotone (fun t => init t ω)
  init_rcont : ∀ ω t, ∃ δ > 0, ∀ s, t ≤ s → s < t + δ → init s ω = init t ω
  init_bdd : ∀ ω, ∃ n : ℕ, ∀ t, init t ω ≤ n
  U_adapted : ∀ t, Measurable[S.𝓕 t] (U t)
  U_nonpos : ∀ ω t, t < 0 → U t ω = 0
  U_mono : ∀ ω, Monotone (fun t => U t ω)
  U_rcont : ∀ ω t, ∃ δ > 0, ∀ s, t ≤ s → s < t + δ → U s ω = U t ω

/-- The left limit `f(t-) = sup_{s < t} f(s)` of a nondecreasing path. -/
def leftLim (f : ℝ → ℕ) (t : ℝ) : ℕ :=
  sSup (f '' Set.Iio t)

/-- Units delivered by time `t`: initial supply plus units ordered by time `t - L`. -/
def delivered (L : ℝ) (init U : ℝ → ℕ) (t : ℝ) : ℕ :=
  init t + U (t - L)

open Classical in
/-- Number of demands served in `(0, t]`. Demand epochs (jumps of `N`) are processed in
increasing order; at an epoch `τ` with `N(τ) - N(τ-)` arrivals, as many are served as the
on-hand stock just before `τ` allows, namely the units delivered strictly before `τ` minus the
demands already served. The remaining arrivals are lost. -/
def servedPath (L : ℝ) (init U N : ℝ → ℕ) (t : ℝ) : ℕ :=
  let E : Set ℝ := {τ | τ ∈ Set.Ioc 0 t ∧ leftLim N τ < N τ}
  if hE : E.Finite then
    (hE.toFinset.sort (· ≤ ·)).foldl
      (fun acc τ => acc + min (N τ - leftLim N τ) (leftLim init τ + leftLim U (τ - L) - acc)) 0
  else 0

/-- Number of positive orders placed in `[0, T]` (jump epochs of the cumulative order path). -/
def orderCount (U : ℝ → ℕ) (T : ℝ) : ℕ :=
  Set.ncard {t | t ∈ Set.Icc 0 T ∧ leftLim U t < U t}

variable {lam : ℝ} {S : DemandSpace lam}

/-- Demands served in `(0, t]` under `π`. -/
def Policy.served (L : ℝ) (π : Policy S) (t : ℝ) (ω : S.Ω) : ℕ :=
  servedPath L (fun s => π.init s ω) (fun s => π.U s ω) (fun s => S.N s ω) t

/-- On-hand inventory `X(t)`: units delivered by `t` minus demands served by `t`. -/
def Policy.onHand (L : ℝ) (π : Policy S) (t : ℝ) (ω : S.Ω) : ℕ :=
  delivered L (fun s => π.init s ω) (fun s => π.U s ω) t - π.served L t ω

/-- Demands lost in `(0, t]`: `𝒰(t) = N(t) - 𝒜(t)`. -/
def Policy.lost (L : ℝ) (π : Policy S) (t : ℝ) (ω : S.Ω) : ℕ :=
  S.N t ω - π.served L t ω

/-- Number `O(T)` of positive orders placed in `[0, T]`. -/
def Policy.orders (π : Policy S) (T : ℝ) (ω : S.Ω) : ℕ :=
  orderCount (fun s => π.U s ω) T

/-- Realized cost on `[0, T]`: `h ∫_0^T X(t) dt + p 𝒰(T) + K O(T)`. -/
def Policy.horizonCost (L h p K : ℝ) (π : Policy S) (T : ℝ) (ω : S.Ω) : ℝ≥0∞ :=
  ENNReal.ofReal h * (∫⁻ t in Set.Icc 0 T, (π.onHand L t ω : ℝ≥0∞))
    + ENNReal.ofReal p * (π.lost L T ω : ℝ≥0∞)
    + ENNReal.ofReal K * (π.orders T ω : ℝ≥0∞)

/-- Long-run average cost `C(π) = limsup_{T → ∞} T⁻¹ E[h ∫_0^T X dt + p 𝒰(T) + K O(T)]`
(eq. (3)). -/
def Policy.avgCost (L h p K : ℝ) (π : Policy S) : ℝ≥0∞ :=
  limsup (fun T : ℝ => (∫⁻ ω, π.horizonCost L h p K T ω ∂S.ν) / ENNReal.ofReal T) atTop

/-- Expected holding `E ∫_0^T X(t) dt`. -/
def Policy.expectedHolding (L : ℝ) (π : Policy S) (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (∫⁻ t in Set.Icc 0 T, (π.onHand L t ω : ℝ≥0∞)) ∂S.ν

/-- Expected number of positive orders `E O(T)`. -/
def Policy.expectedOrders (π : Policy S) (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (π.orders T ω : ℝ≥0∞) ∂S.ν

/-- Expected number of served demands `E 𝒜(T)`. -/
def Policy.expectedServed (L : ℝ) (π : Policy S) (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (π.served L T ω : ℝ≥0∞) ∂S.ν

/-- The policy starts physically empty: no initial supply. -/
def Policy.EmptyStart (π : Policy S) : Prop :=
  ∀ ω t, π.init t ω = 0

end LostSalesRQ

namespace LostSalesRQ

/-- The unrestricted optimum `OPT` (eq. (3)): the infimum of the long-run average cost over all
admissible policies on every demand environment of rate `lam`. -/
def OPT (lam L h p K : ℝ) : ℝ≥0∞ :=
  ⨅ (S : DemandSpace lam) (π : Policy S), π.avgCost L h p K

/-- Normalized optimum `OPT_k(μ, a)`: unit demand rate, unit holding cost, lead time `μ`,
lost-sales penalty `a`, setup cost `k` (Section 3.2). -/
def OPTk (μ a k : ℝ) : ℝ≥0∞ :=
  OPT 1 μ 1 a k

variable {lam : ℝ}

/-- The empty-start policy that never orders. -/
def noOrderPolicy (S : DemandSpace lam) : Policy S where
  init := fun _ _ => 0
  U := fun _ _ => 0
  init_meas := fun _ => measurable_const
  init_nonpos := fun _ _ _ => rfl
  init_mono := fun _ => monotone_const
  init_rcont := fun _ _ => ⟨1, one_pos, fun _ _ _ => rfl⟩
  init_bdd := fun _ => ⟨0, fun _ => le_rfl⟩
  U_adapted := fun _ => measurable_const
  U_nonpos := fun _ _ _ => rfl
  U_mono := fun _ => monotone_const
  U_rcont := fun _ _ => ⟨1, one_pos, fun _ _ _ => rfl⟩

/-- `π` follows the classical `(r, Q)` rule (Section 3.3): it starts with `r + Q` units on hand
and an empty pipeline, and a served demand that lowers the inventory position from `r + 1` to `r`
triggers an immediate order of `Q` units. Equivalently, the cumulative order quantity is
`Q ⌊𝒜(t)/Q⌋`, where `𝒜(t)` is the number of demands served in `(0, t]`. -/
def IsRQPolicy {S : DemandSpace lam} (L : ℝ) (r Q : ℕ) (π : Policy S) : Prop :=
  (∀ ω t, π.init t ω = if 0 ≤ t then r + Q else 0) ∧
  ∀ ω t, π.U t ω = Q * (π.served L t ω / Q)

/-- The classical family `Π_rQ`: every `(r, Q)` policy with integers `r ≥ 0`, `Q ≥ 1`, together
with the empty-start no-order policy. -/
def rQFamily (S : DemandSpace lam) (L : ℝ) : Set (Policy S) :=
  {π | ∃ r Q : ℕ, 1 ≤ Q ∧ IsRQPolicy L r Q π} ∪ {noOrderPolicy S}

/-- The integer base-stock family `Π_S`: base stock `j ≥ 1` is the `(j - 1, 1)` rule, and level
`0` is the no-order policy. -/
def baseStockFamily (S : DemandSpace lam) (L : ℝ) : Set (Policy S) :=
  {π | ∃ j : ℕ, 1 ≤ j ∧ IsRQPolicy L (j - 1) 1 π} ∪ {noOrderPolicy S}

/-- `inf_{π ∈ Π_rQ} C(π)` on the demand environment `S`. -/
def rQFamilyCost (S : DemandSpace lam) (L h p K : ℝ) : ℝ≥0∞ :=
  ⨅ π ∈ rQFamily S L, π.avgCost L h p K

/-- `inf_{π ∈ Π_S} C(π)` at zero setup cost on the demand environment `S`. -/
def baseStockFamilyCost (S : DemandSpace lam) (L h p : ℝ) : ℝ≥0∞ :=
  ⨅ π ∈ baseStockFamily S L, π.avgCost L h p 0

open Classical in
/-- `π` is a policy returned by the selection rule of Corollary 1 for normalized data
`(μ, a, k)` and base-stock level `Sstar`: if `Sstar ≥ 1` and `U_μ(a) + b_k < a`, it follows the
`(Sstar - 1, Q_k)` rule; otherwise it is the no-order policy. -/
def IsSelectedPolicy {S : DemandSpace lam} (L μ a k : ℝ) (Sstar : ℕ) (π : Policy S) : Prop :=
  if 1 ≤ Sstar ∧ minBaseStockCost μ a + batchSurcharge k < a then
    IsRQPolicy L (Sstar - 1) (lotSize k) π
  else π = noOrderPolicy S

end LostSalesRQ


