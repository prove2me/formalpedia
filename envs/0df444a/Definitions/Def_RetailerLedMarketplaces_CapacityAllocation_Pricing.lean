-- Prove2me | Definitions.Def_RetailerLedMarketplaces_CapacityAllocation_Pricing
-- name    : RetailerLedMarketplaces_CapacityAllocation_Pricing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:43:04.055632+00:00
-- url     : https://prove2.me/theorems/f7f14ac9-60cc-4c84-a4d5-2bba717c55ce
-- title:
--   Actual pricing strategies, demand, payoffs and selected seller entry
-- statement:
--   In each product market, consumers buy only available offers priced at most their valuation $v$. The share $\lambda$ follows the retailer's steering; the remaining share buys the cheaper offer, with price ties favoring the retailer. The published primitive quantities and payoffs implement these rules, including cost on units actually sold and fees only on third-party sales.
--
--   For a viable seller, $(1-f)v\ge c$, the selected monopoly quote is $v$. The selected joint-entry quote is
--
--   $$\bar p_T(v)=\frac{\lambda v+c(1-\lambda)}{1-f(1-\lambda)},$$
--
--   with $\bar p_T=v$ when the denominator vanishes. An unviable seller selects a quote $v+1$ and makes no sales. The retailer's response is an explicit comparison of primitive payoffs at valuation, matching and no-sale prices, with both steering choices. It is defined at every real third-party quote, and gives the valuation/self-steering action priority on indifference. Sole-seller steering is likewise defined at every quote, including negative quotes.
--
--   Actual outcomes and quantities are computed from those strategies for each pair of entry choices. Pricing optimality uses the published deviation inequalities: the retailer responds optimally after every quote, and the seller cannot improve her payoff by another quote. A separate output report collects the source prices, actual quantities, profit formulas and nonnegativity. It does not define equilibrium by those desired formulas.
--
--   The selected seller entry set is $E=\{v\ge c:(1-f)v\ge c\}$ for $f<1$, and $E=\varnothing$ at $f=1$, including zero cost. Thus zero-profit entry is selected at ordinary thresholds and zero-profit nonentry at foreclosure.
-- source:
--   Hervas-Drane and Shelegia, Retailer-Led Marketplaces, Management Science, Articles in Advance (2025), doi:10.1287/mnsc.2023.00315, printed pp. 4–6, 13 (PDF pp. 6–8, 15), Sections 2–4, Proposition 1, Lemma 1 and proof of Proposition 1

import Definitions.Def_RetailerLedMarketplaces_CapacityAllocation_Model

open MeasureTheory Set RetailerMarketplace.Entry
noncomputable section

namespace RetailerLedMarketplaces.CapacityAllocation
attribute [local instance] Classical.propDecidable

/-- The only undefined printed price ratio has its explicit price-v completion. -/
def safePrice (p : Parameters) (v : ℝ) : ℝ :=
  if 1 - p.f * (1 - p.lam) = 0 then v else pbarT p.c p.f p.lam v

def Viable (p : Parameters) (v : ℝ) : Prop := p.c ≤ (1 - p.f) * v

/-- At an unviable history T chooses no sales. Prices are unrestricted reals as in PricingGame. -/
def sellerPriceSBT (p : Parameters) (v : ℝ) : ℝ :=
  if Viable p v then v else v + 1

def sellerPriceSBMT (p : Parameters) (v : ℝ) : ℝ :=
  if Viable p v then safePrice p v else v + 1

/-- Steering is a strategy at every possible quote, including negative off-path quotes. -/
def steeringSBT (p : Parameters) (q : ℝ) : Steer :=
  if 0 ≤ p.f * q then .T else .M

/-- Finite comparison of primitive payoffs, retaining the first candidate on indifference. -/
def betterResponse (p : Parameters) (v q : ℝ) (a b : ℝ × Steer) : ℝ × Steer :=
  if uM p.c p.f p.lam v q b.1 b.2 ≤ uM p.c p.f p.lam v q a.1 a.2 then a else b

/-- A price/steering response at every T quote, defined without any optimality assumption.
The candidates are the valuation, matching and no-sale prices, with both steering choices.
The valuation/self-steering candidate has first priority on indifference. -/
def responseSBMT (p : Parameters) (v q : ℝ) : ℝ × Steer :=
  betterResponse p v q (v, .M)
    (betterResponse p v q (v, .T)
      (betterResponse p v q (q, .M)
        (betterResponse p v q (q, .T)
          (betterResponse p v q (v + 1, .M) (v + 1, .T)))))

/-- Primitive actual M payoff for each pair of entry decisions. -/
def outcomeM (p : Parameters) (v : ℝ) (m t : Bool) : ℝ :=
  if m then
    if t then
      let q := sellerPriceSBMT p v
      let r := responseSBMT p v q
      uM p.c p.f p.lam v q r.1 r.2
    else uM_SBM p.c p.lam v v .M
  else if t then
    let q := sellerPriceSBT p v
    uM_SBT p.f p.lam v q (steeringSBT p q)
  else 0

/-- Primitive actual T payoff; absence gives zero, never a counterfactual sale. -/
def outcomeT (p : Parameters) (v : ℝ) (m t : Bool) : ℝ :=
  if t then
    if m then
      let q := sellerPriceSBMT p v
      let r := responseSBMT p v q
      uT p.c p.f p.lam v q r.1 r.2
    else
      let q := sellerPriceSBT p v
      uT_SBT p.c p.f p.lam v q (steeringSBT p q)
  else 0

/-- Selected actual quantities, obeying the primitive tie and availability rules. -/
def quantityM (p : Parameters) (v : ℝ) (m t : Bool) : ℝ :=
  if m then
    if t then
      let q := sellerPriceSBMT p v
      let r := responseSBMT p v q
      qM p.lam v q r.1 r.2
    else qM_SBM p.lam v v .M
  else 0

def quantityT (p : Parameters) (v : ℝ) (m t : Bool) : ℝ :=
  if t then
    if m then
      let q := sellerPriceSBMT p v
      let r := responseSBMT p v q
      qT p.lam v q r.1 r.2
    else
      let q := sellerPriceSBT p v
      qT_SBT p.lam v q (steeringSBT p q)
  else 0

/-- Sequential deviations, independently of entry thresholds and modes. -/
def PricingOptimal (p : Parameters) (v : ℝ) : Prop :=
  IsOptSBM p.c p.lam v v .M ∧
  IsSPNE_SBT p.c p.f p.lam v (sellerPriceSBT p v) (steeringSBT p) ∧
  IsSPNE_SBMT p.c p.f p.lam v (sellerPriceSBMT p v) (responseSBMT p v)

/-- Output report for Proposition 1; it is not the definition of equilibrium. -/
def PricingReport (p : Parameters) (v : ℝ) : Prop :=
  PricingOptimal p v ∧
  quantityM p v true false = 1 ∧ outcomeM p v true false = piSBM p.c v ∧
  outcomeT p v true false = 0 ∧
  (Viable p v →
    sellerPriceSBT p v = v ∧ steeringSBT p v = .T ∧
    quantityT p v false true = 1 ∧
    outcomeM p v false true = piSBT_M p.f v ∧
    outcomeT p v false true = piSBT_T p.c p.f v ∧
    sellerPriceSBMT p v = safePrice p v ∧
    responseSBMT p v (safePrice p v) = (v, .M) ∧
    outcomeM p v true true = p.lam * (v - p.c) + (1 - p.lam) * p.f * safePrice p v ∧
    outcomeT p v true true = (1 - p.lam) * ((1 - p.f) * safePrice p v - p.c) ∧
    safePrice p v ≤ v ∧
    (safePrice p v < v → quantityM p v true true = p.lam ∧
      quantityT p v true true = 1 - p.lam) ∧
    (safePrice p v = v → quantityM p v true true = 1 ∧ quantityT p v true true = 0)) ∧
  (¬ Viable p v →
    quantityT p v false true = 0 ∧ quantityT p v true true = 0 ∧
    outcomeT p v false true = 0 ∧ outcomeT p v true true = 0 ∧
    outcomeM p v false true = 0 ∧ outcomeM p v true true = v - p.c) ∧
  (∀ m t : Bool, 0 ≤ outcomeM p v m t ∧ 0 ≤ outcomeT p v m t)

/-- Selected seller entry includes zero-profit entry, except for fee-one foreclosure. -/
def sellerEntry (p : Parameters) : Set ℝ :=
  if p.f = 1 then ∅ else {v | p.c ≤ v ∧ Viable p v}

end RetailerLedMarketplaces.CapacityAllocation


