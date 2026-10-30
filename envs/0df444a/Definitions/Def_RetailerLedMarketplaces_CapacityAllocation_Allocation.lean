-- Prove2me | Definitions.Def_RetailerLedMarketplaces_CapacityAllocation_Allocation
-- name    : RetailerLedMarketplaces_CapacityAllocation_Allocation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:43:52.579598+00:00
-- url     : https://prove2.me/theorems/291318b0-49c2-482e-81c9-7fda940d0d50
-- title:
--   Measurable capacity, extended thresholds and sequential entry incentives
-- statement:
--   For $f<1$, set $v_T=c/(1-f)$ and $v^*=c\lambda/((1-f)^2(\lambda-f(1-\lambda)))$, using the published algebraic definitions. These real formulas occur only in their nonsingular theorem branches. At $f=1$, set the extended seller threshold to $+\infty$ and the capacity threshold to zero. Otherwise $\underline k=1-G(v^*)$, independently of capacity $k$.
--
--   For $0<k<1$, the canonical upper quantile is the extended supremum of $x\ge c$ with $G(x)\le1-k$. At $k=0$ it is $+\infty$; at $k=1$ it is $c$. An extended upper tail contains the real products at least as large as the cutoff, restricted to $[c,\infty)$. Mode I uses the larger of the canonical cutoff and $v_T$ as a representative of the same quantile plateau; this only changes null products when the canonical full-capacity endpoint lies below $v_T$.
--
--   An admissible retailer assortment is any measurable $A\subseteq[c,\infty)$ with $\mu(A)\le k$. For a seller-entry history $E$, actual retailer profit is
--
--   $$\Pi(E,A)=\int \pi_M(v;\mathbf1_A(v),\mathbf1_E(v))\,d\mu(v)\in[0,+\infty].$$
--
--   The integrand comes from primitive demand and the explicit pricing strategies. The nonnegative extended integral retains infinite profits; nonnegativity and measurability are asserted by results rather than hidden by clipping. Retailer optimality compares every admissible measurable assortment. A sequential entry equilibrium supplies an optimal retailer response at every measurable seller history, optimal pricing at every quote, and each seller's deviation inequality evaluated after the retailer responds to her changed entry history. No mode condition, threshold solution or given optimizer is a premise of this equilibrium predicate.
--
--   The finite per-product gain is $\Delta(v)=\pi_M(v;1,1)-\pi_M(v;0,1)$. The threshold system is
--
--   $$c\le v_L\le v_T\le v_H\le v^*,\quad v_L-c=\Delta(v_H),\quad 1-G(v_H)+G(v_T)-G(v_L)=k.$$
--
--   The corresponding assortment is $[v_L,v_T)\cup[v_H,\infty)$. Configurations are computed from entry membership alone. Equality modulo null products is measured by the symmetric difference. Baseline and incremental profits are separate extended integrals; no infinite totals are subtracted.
-- source:
--   Hervas-Drane and Shelegia, Retailer-Led Marketplaces, Management Science, Articles in Advance (2025), doi:10.1287/mnsc.2023.00315, printed pp. 4–7, 13–15 (PDF pp. 6–9, 15–17), Sections 2–4, (1), (3), Proposition 2 and its Appendix A proof

import Definitions.Def_RetailerLedMarketplaces_CapacityAllocation_Pricing

open MeasureTheory Set RetailerMarketplace.Entry
noncomputable section

namespace RetailerLedMarketplaces.CapacityAllocation
attribute [local instance] Classical.propDecidable

/-- These real formulas are used only on their nonsingular domains in the assertions. -/
def sellerThresholdReal (p : Parameters) : ℝ := vT p.c p.f

def sellerThreshold (p : Parameters) : EReal :=
  if p.f = 1 then ⊤ else (sellerThresholdReal p : EReal)

def crossoverReal (p : Parameters) : ℝ := vStar p.c p.f p.lam

/-- Fixed-fee capacity threshold, independent of the capacity to be allocated. -/
def capacityThreshold (p : Parameters) (d : ProductLaw p.c) : ℝ :=
  if p.f = 1 then 0 else 1 - cdf d (crossoverReal p)

/-- Upper generalized inverse on 0<k<1; explicit endpoint choices at both 0 and 1. -/
def capacityQuantile (p : Parameters) (d : ProductLaw p.c) (k : ℝ) : EReal :=
  if k = 0 then ⊤ else if k = 1 then (p.c : EReal) else
    sSup {x : EReal | ∃ v : ℝ, p.c ≤ v ∧ cdf d v ≤ 1 - k ∧ x = (v : EReal)}

/-- Real products above an extended threshold; +∞ gives the empty set. -/
def upperTail (p : Parameters) (a : EReal) : Set ℝ :=
  {v | p.c ≤ v ∧ a ≤ (v : EReal)}

def modeTwoAssortment (p : Parameters) (l h : ℝ) : Set ℝ :=
  Ico l (sellerThresholdReal p) ∪ Ici h

/-- Mode-I representative of the quantile plateau: at full capacity it may differ
from the canonical endpoint c only on a zero-density initial gap. -/
def modeOneCutoff (p : Parameters) (d : ProductLaw p.c) (k : ℝ) : EReal :=
  max (capacityQuantile p d k) (sellerThreshold p)

/-- Actual finite per-product gain, never subtraction of extended total profits. -/
def entryGain (p : Parameters) (v : ℝ) : ℝ :=
  outcomeM p v true true - outcomeM p v false true

/-- Any measurable assortment within the product space is an admissible deviation. -/
def Feasible (p : Parameters) (d : ProductLaw p.c) (k : ℝ) (a : Set ℝ) : Prop :=
  MeasurableSet a ∧ a ⊆ Ici p.c ∧ d.measure a ≤ ENNReal.ofReal k

/-- ofReal is used as an embedding on nonnegative actual profits, which are asserted separately. -/
def totalProfit (p : Parameters) (d : ProductLaw p.c) (e a : Set ℝ) : ENNReal :=
  ∫⁻ v, ENNReal.ofReal (outcomeM p v (decide (v ∈ a)) (decide (v ∈ e))) ∂d.measure

/-- The definition has no interval restriction, no assumed optimizer and no mode condition. -/
def RetailerOptimal (p : Parameters) (d : ProductLaw p.c) (k : ℝ)
    (e a : Set ℝ) : Prop :=
  Feasible p d k a ∧
  Measurable (fun v => outcomeM p v (decide (v ∈ a)) (decide (v ∈ e))) ∧
  (∀ v ∈ Ici p.c, 0 ≤ outcomeM p v (decide (v ∈ a)) (decide (v ∈ e))) ∧
  ∀ b : Set ℝ, Feasible p d k b → totalProfit p d e b ≤ totalProfit p d e a

/-- The history seen by M after a single seller changes her entry choice. -/
def changedHistory (e : Set ℝ) (v : ℝ) : Set ℝ :=
  if v ∈ e then e \ {v} else insert v e

/-- Each seller compares her actual continuation with her unilateral deviation and ensuing M response. -/
def SellerStable (p : Parameters) (e a : Set ℝ) (plan : Set ℝ → Set ℝ) : Prop :=
  ∀ v ∈ Ici p.c,
    outcomeT p v (decide (v ∈ plan (changedHistory e v))) (!(decide (v ∈ e))) ≤
      outcomeT p v (decide (v ∈ a)) (decide (v ∈ e))

/-- Sequential rationality after a fixed fee. The plan must be optimal at every measurable
seller history, and pricing responses are optimal at every price, on and off the path. -/
def IsEquilibrium (p : Parameters) (d : ProductLaw p.c) (k : ℝ) (e a : Set ℝ) : Prop :=
  MeasurableSet e ∧ e ⊆ Ici p.c ∧
  (∀ v ∈ Ici p.c, PricingOptimal p v) ∧
  ∃ plan : Set ℝ → Set ℝ,
    plan e = a ∧
    (∀ history : Set ℝ, MeasurableSet history → history ⊆ Ici p.c →
      RetailerOptimal p d k history (plan history)) ∧
    SellerStable p e a plan

/-- Both source equations; closed endpoints are necessary at full capacity. -/
def ThresholdSystem (p : Parameters) (d : ProductLaw p.c) (k l h : ℝ) : Prop :=
  l ∈ Icc p.c (sellerThresholdReal p) ∧
  h ∈ Icc (sellerThresholdReal p) (crossoverReal p) ∧
  l - p.c = entryGain p h ∧
  (1 - cdf d h) + (cdf d (sellerThresholdReal p) - cdf d l) = k

/-- Equality of product assortments modulo null differences, not equality of cutoffs in gaps. -/
def SameProducts (p : Parameters) (d : ProductLaw p.c) (a b : Set ℝ) : Prop :=
  d.measure ((a \ b) ∪ (b \ a)) = 0

inductive Configuration where
  | empty | sbm | sbt | sbmt
  deriving DecidableEq

/-- Configuration is computed solely from actual entry decisions. -/
def configuration (e a : Set ℝ) (v : ℝ) : Configuration :=
  if v ∈ a then (if v ∈ e then .sbmt else .sbm)
  else (if v ∈ e then .sbt else .empty)

/-- Formula used for fee comparisons on the viable nonsingular branch. -/
def marginalFormula (c f lam v : ℝ) : ℝ :=
  (v - c / (1 - f)) * ((1 - f) * (lam - f * (1 - lam))) / (1 - f * (1 - lam))

def baselineProfit (p : Parameters) (d : ProductLaw p.c) : ENNReal :=
  totalProfit p d (sellerEntry p) ∅

def incrementalProfit (p : Parameters) (d : ProductLaw p.c) (a : Set ℝ) : ENNReal :=
  ∫⁻ v in a, ENNReal.ofReal
    (if v ∈ sellerEntry p then entryGain p v else piSBM p.c v) ∂d.measure

end RetailerLedMarketplaces.CapacityAllocation


