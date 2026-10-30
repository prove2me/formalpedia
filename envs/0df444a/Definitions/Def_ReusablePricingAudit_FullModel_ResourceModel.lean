-- Prove2me | Definitions.Def_ReusablePricingAudit_FullModel_ResourceModel
-- name    : ReusablePricingAudit_FullModel_ResourceModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:48:25.088706+00:00
-- url     : https://prove2.me/theorems/b67d44fa-3adc-49b5-8f5a-d4b120e3dc75
-- title:
--   Physical reusable-resource system and its global dynamic benchmark
-- statement:
--   An instance has $C\ge1$ reusable units, market rate $\Lambda>0$, service rate $\mu>0$, cost $c>0$, and an i.i.d. valuation law $F$. Each positive feasible rate $l\in(0,\Lambda]$ has its inverse price $p(l)$, satisfying $\Pr\{V>p(l)\}=l/\Lambda$. The no-offer action has rate zero. The net arrival reward $r(0)=0$, $r(l)=l(p(l)-c)$ for $l>0$, is concave on $[0,\Lambda]$. Weights $\alpha_j\ge0$ sum to one.
--
--   The primitive marked clock has rate $\Lambda+C\mu$. Its arrival marks generate potential customers at rate $\Lambda$, willing customers according to their valuations, and sales only when a unit is free. In state $q$ of free inventory, service completion has rate $(C-q)\mu$. A sale decreases $q$ by one; a completion increases it by one; blocked customers leave. Silent ticks are hidden. The resulting processes are denoted $A$, $B^\pi$, $D^\pi$, and $Q^\pi$ respectively for potential arrivals, willing arrivals, accepted sales, and free units.
--
--   For any observable-history pricing policy $\pi$, from initial inventory $q_0\in\{0,\ldots,C\}$, define
--   $$\mathcal P^\pi=\liminf_{T\to\infty}\frac1T\mathbb E\!\left[\sum_{\tau\le T:\,\text{sale at }\tau}(p(l_\tau)-c)\right],$$
--   $$\mathcal{MS}^\pi=\liminf_{T\to\infty}\frac{\mathbb E[D^\pi(T)]}{T},\qquad
--   \mathcal{SL}^\pi=\liminf_{T\to\infty}\frac1T\mathbb E\!\left[\int_0^T1_{\{Q^\pi(t)>0\}}dt\right].$$
--   The objective is $W(\pi)=\alpha_1\mathcal P^\pi+\alpha_2\mathcal{MS}^\pi+\alpha_3\mathcal{SL}^\pi$, and $V^*=\sup_{\pi\in\Pi}W(\pi)$. A globally optimal policy satisfies $W(\rho)\le W(\pi^*)$ for every admissible non-anticipating randomized control $\rho$.
--
--   This is the physical benchmark for the guarantee. Neither stationary reduction nor any guarantee is a structure field. Static and stationary rules are explicit members of the same policy class, and profit retains its sign.
--
--   Differences from the source:
--   - encoding: Poisson customers and independent exponential service times with non-anticipating pricing → independent marked exponential clocks, observable event histories, and independent uniform randomization; reason: uniformization generates the same loss-system law; dummy clock ticks are hidden and policies never see future marks
--   - encoding: a rate-zero no-purchase action, possibly at an infinite limiting price → an explicit no-offer action with zero transaction reward and an ignored dummy price at zero; reason: all positive-rate inverse prices are retained, including unbounded limits at zero
--   - encoding: expected real long-run liminf objectives → extended signed Lebesgue expectation and EReal liminf over real horizons; reason: finiteness is a separate theorem conclusion, so nonintegrable integrals or unbounded real suprema cannot silently become zero
--   - reading: N is called an offered-arrival process on p. 8 but units sold on p. 9 and Eq. (6) → market share counts accepted sales D, separately from potential arrivals A and willing arrivals B; reason: with C=μ=Λ=c=1 and uniform demand at rate 1 the offered rate is 1 and sales rate is 1/2; units sold and Eq. (6) select D
--   - generalization: initial inventory is unspecified → every deterministic initial inventory q₀ in {0,…,C}; reason: the exponential model permits every initial free-inventory state; the source instance is included
--   - encoding: availability at an arrival in (1) → test pre-event free inventory and charge only accepted admission jumps; reason: a sale consumes a previously free unit; post-event inventory may be zero even for a valid sale, and the predictable convention agrees with (5)
-- source:
--   Besbes, Elmachtoub and Sun, Static Pricing: Universal Guarantees for Reusable Resources, arXiv:1905.00731v3 (11 February 2020), pp. 7–10, §§2.1–2.3, (1)–(7); p. ec3 (PDF 24), [0,Λ] in (EC.1)

import Mathlib
import Definitions.Def_ReusablePricingAudit_FullModel_JumpProcess
import Definitions.Def_StaticReusable_Guarantee_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace ReusablePricingAudit.FullModel

/-- Source instance, §§2.1–2.2. The price is used only at positive rates; rate zero
is the no-offer action, also permitting an infinite limiting inverse price.
No positivity of margins, strict concavity, or positivity of weights is imposed. -/
structure ResourceInstance where
  C : ℕ
  capacity_pos : 1 ≤ C
  μ : ℝ
  Λ : ℝ
  c : ℝ
  service_pos : 0 < μ
  market_pos : 0 < Λ
  cost_pos : 0 < c
  valuationLaw : Measure ℝ
  valuation_probability : IsProbabilityMeasure valuationLaw
  price : ℝ → ℝ
  inverse_demand : ∀ l ∈ Set.Ioc 0 Λ,
    valuationLaw (Set.Ioi (price l)) = ENNReal.ofReal (l / Λ)
  α₁ : ℝ
  α₂ : ℝ
  α₃ : ℝ
  weight_nonneg : 0 ≤ α₁ ∧ 0 ≤ α₂ ∧ 0 ≤ α₃
  weight_sum : α₁ + α₂ + α₃ = 1
  concave_net_rate : ConcaveOn ℝ (Set.Icc 0 Λ)
    (fun l => if l = 0 then 0 else l * (price l - c))

/-- The entire continuous action interval, including the no-offer endpoint. -/
abbrev Rate (I : ResourceInstance) := Set.Icc (0 : ℝ) I.Λ

/-- Non-anticipating controls on the observable loss-system history, with an
independent random seed. Bounds hold for every history, including null histories. -/
structure PricingPolicy (I : ResourceInstance) extends HistoryControl where
  feasible : ∀ z t q h, rule z t q h ∈ Set.Icc 0 I.Λ

/-- Uniformization rate; it dominates all physical event rates, including boundaries. -/
def uniformRate (I : ResourceInstance) : ℝ := I.Λ + I.C * I.μ

/-- The loss system driven by the general marked clock. The first mark is uniform
on [0,1], the second is a customer valuation independent of that mark. Events:
0 = unwilling potential arrival, 1 = willing but blocked arrival, 2 = accepted
sale, 3 = service completion. Dummy ticks generate no observation. The service
rate in free-inventory state q is (C-q)μ. Future durations are not revealed. -/
noncomputable def resourceSystem (I : ResourceInstance) : JumpSystem (ℝ × ℝ) where
  clockRate := uniformRate I
  clockRate_pos := by
    have h : 0 ≤ (I.C : ℝ) * I.μ := mul_nonneg (Nat.cast_nonneg _) (le_of_lt I.service_pos)
    exact add_pos_of_pos_of_nonneg I.market_pos h
  markLaw := (volume.restrict (Set.Icc (0 : ℝ) 1)).prod I.valuationLaw
  markLaw_probability := by
    have : IsProbabilityMeasure I.valuationLaw := I.valuation_probability
    have : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
      constructor
      simp [Real.volume_Icc]
    infer_instance
  transition := fun q l m => by
    classical
    exact if m.1 < I.Λ / uniformRate I then
      if 0 < l ∧ I.price l < m.2 then
        if 0 < q then (q - 1, some 2) else (q, some 1)
      else (q, some 0)
    else if q < I.C ∧ m.1 < (I.Λ + (I.C - q) * I.μ) / uniformRate I then
      (q + 1, some 3)
    else (q, none)

/-- The independent primitive law of the resource system. -/
noncomputable def resourceLaw (I : ResourceInstance) : Measure (Experiment (ℝ × ℝ)) :=
  experimentLaw (resourceSystem I)

/-- The number of free units, obtained from the physical transition recursion. -/
noncomputable def freeUnits (I : ResourceInstance) (q₀ : Fin (I.C + 1))
    (π : PricingPolicy I) (ω : Experiment (ℝ × ℝ)) (t : ℝ) : ℕ :=
  stateAt (resourceSystem I) π.toHistoryControl q₀.val ω t

/-- Predictable pre-event rate and inventory. Dummy uniformization ticks are
not observed by the controller and do not change either argument. -/
noncomputable def preDecision (I : ResourceInstance) (q₀ : Fin (I.C + 1))
    (π : PricingPolicy I) (ω : Experiment (ℝ × ℝ)) (t : ℝ) : ℕ × ℝ :=
  let old := evolution (resourceSystem I) π.toHistoryControl q₀.val ω (eventsBefore ω.2 t)
  (old.1, π.rule ω.1 t old.1 old.2)

/-- Finite net arrival reward rate, with the actual no-offer extension at zero. -/
noncomputable def netRate (I : ResourceInstance) (l : ℝ) : ℝ :=
  if l = 0 then 0 else l * (I.price l - I.c)

/-- Counts of observed event codes up to time T. -/
noncomputable def eventCount (I : ResourceInstance) (q₀ : Fin (I.C + 1))
    (π : PricingPolicy I) (ω : Experiment (ℝ × ℝ)) (T : ℝ)
    (codes : Finset ℕ) : ℕ := by
  classical
  exact ((Finset.range (eventsBy ω.2 T)).filter fun n =>
    ∃ k ∈ codes, observationAtEvent (resourceSystem I) π.toHistoryControl q₀.val ω n = some k).card

/-- A: all potential arrivals, B: willing arrivals, D: accepted sales. They are
different processes; B under an adaptive policy need not have independent increments. -/
noncomputable def potentialArrivals (I : ResourceInstance) (q₀ : Fin (I.C + 1))
    (π : PricingPolicy I) (ω : Experiment (ℝ × ℝ)) (T : ℝ) : ℕ :=
  eventCount I q₀ π ω T {0, 1, 2}

noncomputable def willingArrivals (I : ResourceInstance) (q₀ : Fin (I.C + 1))
    (π : PricingPolicy I) (ω : Experiment (ℝ × ℝ)) (T : ℝ) : ℕ :=
  eventCount I q₀ π ω T {1, 2}

noncomputable def acceptedSales (I : ResourceInstance) (q₀ : Fin (I.C + 1))
    (π : PricingPolicy I) (ω : Experiment (ℝ × ℝ)) (T : ℝ) : ℕ :=
  eventCount I q₀ π ω T {2}

/-- Actual total transaction margin up to T; only accepted sales pay. A zero-rate
action never creates a sale, so the unspecified value price 0 is never charged. -/
noncomputable def transactionProfit (I : ResourceInstance) (q₀ : Fin (I.C + 1))
    (π : PricingPolicy I) (ω : Experiment (ℝ × ℝ)) (T : ℝ) : ℝ := by
  classical
  exact ∑ n ∈ Finset.range (eventsBy ω.2 T),
    if observationAtEvent (resourceSystem I) π.toHistoryControl q₀.val ω n = some 2 then
      I.price (actionAtEvent (resourceSystem I) π.toHistoryControl q₀.val ω n) - I.c
    else 0

/-- Actual available time, not the admission probability or sales fraction. -/
noncomputable def availableTime (I : ResourceInstance) (q₀ : Fin (I.C + 1))
    (π : PricingPolicy I) (ω : Experiment (ℝ × ℝ)) (T : ℝ) : ℝ≥0∞ := by
  classical
  exact ∫⁻ t in Set.Ioc 0 T, if 0 < freeUnits I q₀ π ω t then 1 else 0

/-- The source's expected long-run liminf metrics, taken over all positive real
horizons tending to infinity. Extended values avoid default real liminf/integrals.
Finiteness is a theorem about the model, not an admissibility assumption. -/
noncomputable def profitRate (I : ResourceInstance) (q₀ : Fin (I.C + 1))
    (π : PricingPolicy I) : EReal :=
  liminf (fun T : ℝ => ((T⁻¹ : ℝ) : EReal) *
    signedExpectation (resourceLaw I) (fun ω => transactionProfit I q₀ π ω T)) atTop

noncomputable def salesRate (I : ResourceInstance) (q₀ : Fin (I.C + 1))
    (π : PricingPolicy I) : EReal :=
  liminf (fun T : ℝ => ((T⁻¹ : ℝ) : EReal) *
    ((∫⁻ ω, (acceptedSales I q₀ π ω T : ℝ≥0∞) ∂resourceLaw I) : EReal)) atTop

noncomputable def serviceLevel (I : ResourceInstance) (q₀ : Fin (I.C + 1))
    (π : PricingPolicy I) : EReal :=
  liminf (fun T : ℝ => ((T⁻¹ : ℝ) : EReal) *
    ((∫⁻ ω, availableTime I q₀ π ω T ∂resourceLaw I) : EReal)) atTop

noncomputable def weightedValue (I : ResourceInstance) (q₀ : Fin (I.C + 1))
    (π : PricingPolicy I) : EReal :=
  (I.α₁ : EReal) * profitRate I q₀ π + (I.α₂ : EReal) * salesRate I q₀ π +
    (I.α₃ : EReal) * serviceLevel I q₀ π

/-- Optimality against all admissible history-dependent randomized policies. This
does not assert existence, nor build stationarity or the target bound into optimality. -/
def GloballyOptimal (I : ResourceInstance) (q₀ : Fin (I.C + 1))
    (π : PricingPolicy I) : Prop :=
  ∀ ρ : PricingPolicy I, weightedValue I q₀ ρ ≤ weightedValue I q₀ π

/-- Physical global benchmark, with its actual policy domain, in a complete lattice. -/
noncomputable def benchmark (I : ResourceInstance) (q₀ : Fin (I.C + 1)) : EReal :=
  ⨆ π : PricingPolicy I, weightedValue I q₀ π

/-- One fixed price (or the no-offer action) at every time and every history. -/
def staticPolicy (I : ResourceInstance) (l : Rate I) : PricingPolicy I where
  rule := fun _ _ _ _ => l.val
  measurable_rule := measurable_const
  feasible := fun _ _ _ _ => l.property

/-- A stationary rate at every free-inventory state. Coordinates above C are
irrelevant; their feasible dummy values avoid partial functions on null histories. -/
abbrev StationaryRates (I : ResourceInstance) := ℕ → Rate I

noncomputable def stationaryPolicy (I : ResourceInstance) (lam : StationaryRates I) :
    PricingPolicy I where
  rule := fun _ _ q _ => (lam q).val
  measurable_rule := by fun_prop
  feasible := fun _ _ q _ => (lam q).property

/-- Real representative of inverse demand for the published stationary layer.
The zero value is a dummy: every zero-rate transaction term is zero. -/
noncomputable def auxiliaryPrice (I : ResourceInstance) (l : ℝ) : ℝ := if l = 0 then 0 else I.price l

end ReusablePricingAudit.FullModel


