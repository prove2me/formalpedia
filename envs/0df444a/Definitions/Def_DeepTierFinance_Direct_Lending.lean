-- Prove2me | Definitions.Def_DeepTierFinance_Direct_Lending
-- name    : DeepTierFinance_Direct_Lending
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:21:20.799256+00:00
-- url     : https://prove2.me/theorems/9eef2f5b-0e72-4f2e-8867-e221780531f3
-- title:
--   Competitive loans, supplier cash, and financing decisions
-- statement:
--   Contracts contain a wholesale price and nonnegative AP rate. Bank and manufacturer financing use principal ((y-θ₂)⁺-θ₁)⁺. The success and failure cash expressions are those of (2)–(3), with limited liability applied after debt settlement. CompetitiveBank equates the probability-weighted capped repayments to principal, including a zero principal without division. Supplier offers induce tier-2 responses and maximize tier-1 terminal cash. The traditional response compares the optimized BF/MF cash levels, chooses MF on a tie, and rejects trade if both lose initial capital. Joint BF/MF deviations are also compared: AP is netted from the invoice before the bank receives the remaining assets, following the payment sequence on pp. 8–9. This priority reading agrees with both pure financing formulas. No-trade outcomes explicitly have zero investment and zero incremental profits. Table 1 supplies manufacturer cash flows. The literal auxiliary wholesale bound is v+yb(c|0,e), and the capital upper bound is yb(underline-w|c,e)-c. Boundary responses at θ₂=c are certified for every nonnegative wholesale price used in the contract domain. Raw BF/MF responses are certified at all nonnegative offered prices, including off-equilibrium blockchain offers below the traditional participation bound. W retains its closed θ₁ and half-open θ₂ intervals.
-- source:
--   Dong, Qiu and Xu (2022), Blockchain-Enabled Deep-Tier Supply Chain Finance, MSOM forthcoming, supplied May 2022 manuscript, DOI 10.1287/msom.2022.1123 (published citation basis), Sections 3–4.3, printed/PDF pp. 8–13; assumptions A1–A4, ec9/PDF 39

import Definitions.Def_DeepTierFinance_Direct_Primitives

namespace DeepTierFinance.Direct

noncomputable section

/-- An offered wholesale price and a finite manufacturer AP rate. -/
structure Contract where
  w : ℝ
  r : ℝ
  deriving DecidableEq

/-- Bank-finance or manufacturer-finance decisions at time zero. -/
inductive Finance where
  | bank
  | manufacturer
  deriving DecidableEq

/-- A tier-1 action specifies its AP rate and, for BF, the competitively priced bank rate. -/
structure SupplierOffer where
  rs : ℝ
  rb : ℝ
  deriving DecidableEq

def echelonAdvance (a b y : ℝ) : ℝ := positivePart (advance b y - a)

def successAssets (p : Primitives) (w a b rs y : ℝ) : ℝ :=
  a + echelonAdvance a b y + (w - p.v) - advance b y + (1 + rs) * advance b y

def failureAssets (e w a b y : ℝ) : ℝ :=
  a + echelonAdvance a b y + positivePart (w - e) - advance b y

/-- Expected capped bank repayments equal the principal, including zero-principal cases. -/
def CompetitiveBank (p : Primitives) (e w a b : ℝ) (q : SupplierOffer) (y : ℝ) : Prop :=
  0 ≤ q.rb ∧
  p.P y * min ((1 + q.rb) * echelonAdvance a b y)
    (positivePart (successAssets p w a b q.rs y)) +
  (1 - p.P y) * min ((1 + q.rb) * echelonAdvance a b y)
    (positivePart (failureAssets e w a b y)) = echelonAdvance a b y

/-- Equations (2)-(3), before subtracting tier-1 initial capital. -/
def tier1Cash (p : Primitives) (e w a b rs rk y : ℝ) : ℝ :=
  p.P y * positivePart (successAssets p w a b rs y - (1 + rk) * echelonAdvance a b y) +
  (1 - p.P y) * positivePart (failureAssets e w a b y - (1 + rk) * echelonAdvance a b y)

def offerCash (p : Primitives) (s : InvestmentStrategy) (e a b : ℝ)
    (m : Contract) (k : Finance) (q : SupplierOffer) : ℝ :=
  tier1Cash p e m.w a b q.rs
    (if k = .bank then q.rb else m.r) (s b q.rs)

def OfferFeasible (p : Primitives) (s : InvestmentStrategy) (e a b : ℝ)
    (m : Contract) (k : Finance) (q : SupplierOffer) : Prop :=
  0 ≤ q.rs ∧ InvestmentResponse p b q.rs (s b q.rs) ∧
    (if k = .bank then CompetitiveBank p e m.w a b q (s b q.rs) else 0 ≤ m.r)

/-- Raw maximization in (2) or (3). Participation is checked separately when trade occurs. -/
def OfferOptimal (p : Primitives) (s : InvestmentStrategy) (e a b : ℝ)
    (m : Contract) (k : Finance) (q : SupplierOffer) : Prop :=
  OfferFeasible p s e a b m k q ∧
  ∀ q', OfferFeasible p s e a b m k q' →
    offerCash p s e a b m k q' ≤ offerCash p s e a b m k q

/-- Cash-flow-based response data; no conclusions are imposed as structure fields. -/
structure Responses where
  investment : InvestmentStrategy
  bank : ℝ → ℝ → ℝ → ℝ → SupplierOffer
  manufacturer : ℝ → ℝ → ℝ → Contract → SupplierOffer

/-- Bank target investment, with arguments e,w,theta1,theta2. -/
def bankInvestment (s : Responses) (e w a b : ℝ) : ℝ :=
  s.investment b (s.bank e w a b).rs

/-- Literal lower wholesale-price and capital-domain definitions on pp. 12/ec10. -/
def wholesaleLower (p : Primitives) (s : Responses) (c e : ℝ) : ℝ :=
  p.v + bankInvestment s e c 0 0

def capitalUpper (p : Primitives) (s : Responses) (c e : ℝ) : ℝ :=
  bankInvestment s e (wholesaleLower p s c e) 0 c - c

def CapitalRegion (p : Primitives) (s : Responses) (c e a b : ℝ) : Prop :=
  a ∈ Set.Icc 0 (capitalUpper p s c e) ∧ b ∈ Set.Ico 0 c

/-- Certify every boundary response used by the capital and contract domains. -/
def BoundaryResponses (p : Primitives) (s : Responses) (c e : ℝ) : Prop :=
  OfferOptimal p s.investment e 0 0 ⟨c, 0⟩ .bank (s.bank e c 0 0) ∧
  OfferOptimal p s.investment e 0 c ⟨wholesaleLower p s c e, 0⟩ .bank
    (s.bank e (wholesaleLower p s c e) 0 c) ∧
  ∀ w, 0 ≤ w →
    OfferOptimal p s.investment e 0 c ⟨w, 0⟩ .bank (s.bank e w 0 c)

/-- The bank and manufacturer AP problems at every admissible subgame. -/
def ResponsesRational (p : Primitives) (s : Responses) (c e : ℝ) : Prop :=
  InvestmentRational p c s.investment ∧ BoundaryResponses p s c e ∧
  (∀ a b, CapitalRegion p s c e a b → ∀ m : Contract,
    0 ≤ m.w → 0 ≤ m.r →
    OfferOptimal p s.investment e a b m .bank (s.bank e m.w a b) ∧
    OfferOptimal p s.investment e a b m .manufacturer (s.manufacturer e a b m))

/-- Rejection is explicit; it is not a default investment in an empty argmax. -/
structure Outcome where
  traded : Bool
  financing : Finance
  offer : SupplierOffer
  y : ℝ

/-- Incremental profits, with components 0=M, 1=S1, 2=S2. -/
abbrev Profits := Fin 3 → ℝ

/-- Table 1, with the no-trade alternative returning zero incremental profit. -/
def traditionalProfits (p : Primitives) (e a b : ℝ) (m : Contract) (o : Outcome) : Profits :=
  if o.traded then
    let B := echelonAdvance a b o.y
    let rk := if o.financing = .bank then o.offer.rb else m.r
    let succ := 1 - m.w + (if o.financing = .bank then 0 else m.r * B)
    let fail := if o.financing = .bank then (if e ≤ m.w then 1 - m.w else 0)
      else if e ≤ m.w then 1 - m.w - B + min ((1 + m.r) * B) (m.w - e) else -B
    ![p.P o.y * succ + (1 - p.P o.y) * fail,
      tier1Cash p e m.w a b o.offer.rs rk o.y - a,
      supplierCash p b o.offer.rs o.y - b]
  else ![0, 0, 0]

/-- The source also permits joint BF/MF. AP is netted from the invoice before bank repayment. -/
structure MixedOffer where
  rs : ℝ
  rb : ℝ
  manufacturerPrincipal : ℝ

/-- Residual assets after manufacturer AP settlement, before bank repayment. -/
def mixedAssets (p : Primitives) (e a b : ℝ) (m : Contract) (h : MixedOffer) (y : ℝ) : ℝ × ℝ :=
  (successAssets p m.w a b h.rs y - (1 + m.r) * h.manufacturerPrincipal,
   failureAssets e m.w a b y - (1 + m.r) * h.manufacturerPrincipal)

def MixedFeasible (p : Primitives) (s : InvestmentStrategy) (e a b : ℝ)
    (m : Contract) (h : MixedOffer) : Prop :=
  let y := s b h.rs
  let B := echelonAdvance a b y - h.manufacturerPrincipal
  let A := mixedAssets p e a b m h y
  0 ≤ m.r ∧ 0 ≤ h.rs ∧ 0 ≤ h.rb ∧
  0 ≤ h.manufacturerPrincipal ∧ h.manufacturerPrincipal ≤ echelonAdvance a b y ∧
  InvestmentResponse p b h.rs y ∧
  p.P y * min ((1 + h.rb) * B) (positivePart A.1) +
    (1 - p.P y) * min ((1 + h.rb) * B) (positivePart A.2) = B

def mixedCash (p : Primitives) (s : InvestmentStrategy) (e a b : ℝ)
    (m : Contract) (h : MixedOffer) : ℝ :=
  let y := s b h.rs
  let B := echelonAdvance a b y - h.manufacturerPrincipal
  let A := mixedAssets p e a b m h y
  p.P y * positivePart (A.1 - (1 + h.rb) * B) +
    (1 - p.P y) * positivePart (A.2 - (1 + h.rb) * B)

/-- Compare optimal cash values, choosing MF on a tie and rejecting unprofitable trade. -/
def TraditionalResponse (p : Primitives) (s : Responses) (e a b : ℝ)
    (m : Contract) (o : Outcome) : Prop :=
  let qb := s.bank e m.w a b
  let qm := s.manufacturer e a b m
  let vb := offerCash p s.investment e a b m .bank qb
  let vm := offerCash p s.investment e a b m .manufacturer qm
  (∀ h, MixedFeasible p s.investment e a b m h →
    mixedCash p s.investment e a b m h ≤ max vb vm) ∧
  if max vb vm < a then o.traded = false ∧ o.y = 0 ∧ o.offer = ⟨0, 0⟩ ∧ o.financing = .bank
  else o.traded = true ∧
    (if vb ≤ vm then o.financing = .manufacturer ∧ o.offer = qm
     else o.financing = .bank ∧ o.offer = qb) ∧ o.y = s.investment b o.offer.rs

end
end DeepTierFinance.Direct


