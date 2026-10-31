-- Prove2me | Definitions.Def_DeepTierFinance_Direct_Delegate
-- name    : DeepTierFinance_Direct_Delegate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:23:17.322199+00:00
-- url     : https://prove2.me/theorems/0a173a81-ebb2-411b-abc3-897490a8b96e
-- title:
--   Voluntary delegate financing, adoption, and financing regions
-- statement:
--   A blockchain contract has a wholesale price and either a finite nonnegative AP rate or a tagged no-offer alternative representing infinity. No arithmetic uses infinity, and the no-offer case forces BF. The traditional contract remains available. Tier-1's blockchain offer must lower the tier-2 AP rate and strictly improve tier-2 profit, and tier-1 maximizes its own cash against the complete investment strategy, including joint-financing deviations. Ties between pure modes favor MF. Rejection implements the traditional outcome. Delegate feasibility requires strict improvement for all three players relative to realized traditional profits. DelegateOptimal is an attained global maximum over those response-induced profits. A policy reverts to the traditional contract if no improving menu exists. Separate predicates express strict adoption, fixed-price rate optima, emergency-cost switches, and the traditional financing threshold. Regions I–IV retain exactly the inequalities in Proposition EC.1.
-- source:
--   Dong, Qiu and Xu (2022), Blockchain-Enabled Deep-Tier Supply Chain Finance, MSOM forthcoming, supplied May 2022 manuscript, DOI 10.1287/msom.2022.1123 (published citation basis), Section 5, printed/PDF pp. 16–18; Appendix A, ec4–ec6/PDF 34–36

import Definitions.Def_DeepTierFinance_Direct_Traditional

namespace DeepTierFinance.Direct
noncomputable section

local instance (q : Prop) : Decidable q := Classical.propDecidable q

/-- None is the source's infinity/no-manufacturer-finance offer, never infinite arithmetic. -/
structure BlockchainContract where
  w : ℝ
  rate : Option ℝ
  deriving DecidableEq

def Contract.finite (m : Contract) : BlockchainContract := ⟨m.w, some m.r⟩

def BlockchainContract.cashContract (m : BlockchainContract) : Contract :=
  ⟨m.w, m.rate.getD 0⟩

def BlockchainContract.Valid (_p : Primitives) (m : BlockchainContract) : Prop :=
  0 ≤ m.w ∧ m.w ≤ 1 ∧ ∀ r, m.rate = some r → 0 ≤ r

/-- A delegate offer must improve S2's payoff and fulfill the promised lower AP rate. -/
def DelegateOfferFeasible (p : Primitives) (s : Responses) (T : TraditionalPolicy)
    (e a b : ℝ) (m : BlockchainContract) (k : Finance) (q : SupplierOffer) : Prop :=
  (k = .manufacturer → ∃ r, m.rate = some r) ∧
  OfferFeasible p s.investment e a b m.cashContract k q ∧
  q.rs < (T.response e a b (T.menu e a)).offer.rs ∧
  (realizedBenchmark p T e a b) 2 < supplierCash p b q.rs (s.investment b q.rs) - b

/-- Rational S1 response, with MF on a tie and the old contract available. -/
def DelegateResponse (p : Primitives) (s : Responses) (T : TraditionalPolicy)
    (e a b : ℝ) (m : BlockchainContract) (o : Outcome) : Prop :=
  let old := realizedBenchmark p T e a b
  if ∃ k q, DelegateOfferFeasible p s T e a b m k q ∧
      old 1 < offerCash p s.investment e a b m.cashContract k q - a then
    o.traded = true ∧ DelegateOfferFeasible p s T e a b m o.financing o.offer ∧
    o.y = s.investment b o.offer.rs ∧
    old 1 < offerCash p s.investment e a b m.cashContract o.financing o.offer - a ∧
    (∀ k q, DelegateOfferFeasible p s T e a b m k q →
      offerCash p s.investment e a b m.cashContract k q ≤
      offerCash p s.investment e a b m.cashContract o.financing o.offer) ∧
    (∀ h, MixedFeasible p s.investment e a b m.cashContract h →
      (m.rate = none → h.manufacturerPrincipal = 0) →
      h.rs < (T.response e a b (T.menu e a)).offer.rs →
      old 2 < supplierCash p b h.rs (s.investment b h.rs) - b →
      mixedCash p s.investment e a b m.cashContract h ≤
        offerCash p s.investment e a b m.cashContract o.financing o.offer) ∧
    (o.financing = .bank → ∀ q, DelegateOfferFeasible p s T e a b m .manufacturer q →
      offerCash p s.investment e a b m.cashContract .manufacturer q <
      offerCash p s.investment e a b m.cashContract .bank o.offer)
  else (∀ h, MixedFeasible p s.investment e a b m.cashContract h →
      (m.rate = none → h.manufacturerPrincipal = 0) →
      h.rs < (T.response e a b (T.menu e a)).offer.rs →
      old 2 < supplierCash p b h.rs (s.investment b h.rs) - b →
      mixedCash p s.investment e a b m.cashContract h - a ≤ old 1) ∧
    o.traded = false ∧
    o.offer = (T.response e a b (T.menu e a)).offer ∧
    o.financing = (T.response e a b (T.menu e a)).financing ∧
    o.y = (T.response e a b (T.menu e a)).y

/-- The rejection branch implements the unchanged traditional menu. -/
def delegateProfits (p : Primitives) (T : TraditionalPolicy) (e a b : ℝ)
    (m : BlockchainContract) (o : Outcome) : Profits :=
  if o.traded then traditionalProfits p e a b m.cashContract o
  else realizedBenchmark p T e a b

def StrictGain (old new : Profits) : Prop := ∀ i, old i < new i

structure DelegatePolicy where
  response : ℝ → ℝ → ℝ → BlockchainContract → Outcome
  menu : ℝ → ℝ → ℝ → BlockchainContract

def DelegateFeasible (p : Primitives) (T : TraditionalPolicy) (D : DelegatePolicy)
    (e a b : ℝ) (m : BlockchainContract) : Prop :=
  m.Valid p ∧ StrictGain (realizedBenchmark p T e a b)
    (delegateProfits p T e a b m (D.response e a b m))

/-- At an adopting profile, global maximality is over the actual response-induced payoffs. -/
def DelegateOptimal (p : Primitives) (T : TraditionalPolicy) (D : DelegatePolicy)
    (e a b : ℝ) (m : BlockchainContract) : Prop :=
  DelegateFeasible p T D e a b m ∧ ∀ n, DelegateFeasible p T D e a b n →
    delegateProfits p T e a b n (D.response e a b n) 0 ≤
    delegateProfits p T e a b m (D.response e a b m) 0

def DelegateEquilibrium (p : Primitives) (c : ℝ) (R : ResponseFamily)
    (T : TraditionalPolicy) (D : DelegatePolicy) : Prop :=
  ∀ e, EmergencyCost p e → ∀ a b, CapitalRegion p (R e) c e a b →
    (∀ m, m.Valid p → DelegateResponse p (R e) T e a b m (D.response e a b m)) ∧
    (if ∃ m, DelegateFeasible p T D e a b m then DelegateOptimal p T D e a b (D.menu e a b)
     else D.menu e a b = (T.menu e a).finite)

/-- Actual adoption is a strict payoff comparison, separately for each supplier. -/
def DelegateAdopts (p : Primitives) (T : TraditionalPolicy) (D : DelegatePolicy)
    (e a b : ℝ) (i : Fin 3) : Prop :=
  realizedBenchmark p T e a b i <
    delegateProfits p T e a b (D.menu e a b) (D.response e a b (D.menu e a b)) i

/-- Optimal branch switch; outside the adoption region the traditional menu is used. -/
def DelegateEmergencyThreshold (p : Primitives) (c : ℝ) (R : ResponseFamily)
    (T : TraditionalPolicy) (D : DelegatePolicy) (a b t : ℝ) : Prop :=
  ∀ e, EmergencyCost p e → CapitalRegion p (R e) c e a b →
    DelegateAdopts p T D e a b 1 →
    DelegateOptimal p T D e a b (D.menu e a b) ∧
    (if e ≤ t then (D.menu e a b).w = e else (D.menu e a b).w < e)

/-- Fixed-price optimal rate; no-offer is compared as a genuine BF alternative. -/
def DelegateRateOptimal (p : Primitives) (T : TraditionalPolicy) (D : DelegatePolicy)
    (e a b w : ℝ) (r : Option ℝ) : Prop :=
  DelegateFeasible p T D e a b ⟨w, r⟩ ∧
  ∀ r', DelegateFeasible p T D e a b ⟨w, r'⟩ →
    delegateProfits p T e a b ⟨w, r'⟩ (D.response e a b ⟨w, r'⟩) 0 ≤
    delegateProfits p T e a b ⟨w, r⟩ (D.response e a b ⟨w, r⟩) 0

/-- A financing threshold is tested against the optimized cash values, with the MF tie rule. -/
def PrefersMF (p : Primitives) (s : Responses) (e a b : ℝ) (m : Contract) : Prop :=
  offerCash p s.investment e a b m .bank (s.bank e m.w a b) ≤
    offerCash p s.investment e a b m .manufacturer (s.manufacturer e a b m)

def FinanceThreshold (p : Primitives) (s : Responses) (c e : ℝ)
    (m : Contract) (t : ℝ) : Prop :=
  0 ≤ t ∧ ∀ a b, CapitalRegion p s c e a b →
    (PrefersMF p s e a b m ↔ b ≤ t) ∧
    (∀ h, MixedFeasible p s.investment e a b m h → mixedCash p s.investment e a b m h ≤
      max (offerCash p s.investment e a b m .bank (s.bank e m.w a b))
        (offerCash p s.investment e a b m .manufacturer (s.manufacturer e a b m)))

/-- The four regions in Proposition EC.1, not Figure 4's Omega regions. -/
inductive TransitionRegion where
  | I | II | III | IV
  deriving DecidableEq

def InRegion (N : TransitionRegion) (a b t1 t2 : ℝ) : Prop :=
  match N with
  | .I => a < t1 ∧ t2 < b
  | .II => t1 ≤ a ∧ b ≤ t2
  | .III => a < t1 ∧ b ≤ t2
  | .IV => t1 ≤ a ∧ t2 < b

end
end DeepTierFinance.Direct


