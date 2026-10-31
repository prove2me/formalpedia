-- Prove2me | Definitions.Def_DeepTierFinance_Direct_Characterizations
-- name    : DeepTierFinance_Direct_Characterizations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:25:54.014409+00:00
-- url     : https://prove2.me/theorems/ec312730-29b6-4032-bebb-c88b4ee63f0d
-- title:
--   Implementing rates, first-order equations, and delegate thresholds
-- statement:
--   Solving equation (1) for the rate gives r=vP′(y)/(P′(y)(y-θ₂)+P(y))-1. ImplementedInverse certifies derivative existence, a nonzero denominator, the original equation, and actual global investment optimality. BankFOC and ManufacturerFOC record (EC.1)–(EC.2) as assertions in addition to global cash maximization. DelegateKKT transcribes (EC.11)–(EC.12), including the printed mixed derivative terms, with nonnegative multipliers, complementarity, and derivative existence; it does not define an optimal contract. The finite-rate branch of the fixed-price financing threshold explicitly implements MF and includes KKT and the strict bank-rate comparison; the no-offer branch implements BF. The bank comparison uses the θ₁=0 bank subgame, representing the capital-independent borrowing rate r_b*(w,θ₂), rather than a freely chosen zero-principal rate at a wealthy supplier. Its equality case remains θ₁≥threshold, while Theorem 2 separately retains its printed no-offer condition at θ₁≤threshold. The impossible -P(y)>0 from (EC.13) is never an assumption or a definition.
-- source:
--   Dong, Qiu and Xu (2022), Blockchain-Enabled Deep-Tier Supply Chain Finance, MSOM forthcoming, supplied May 2022 manuscript, DOI 10.1287/msom.2022.1123 (published citation basis), Equation (1), printed/PDF p. 10; Appendix A equations (EC.1)–(EC.2), (EC.11)–(EC.12), ec1/ec4, PDF 31/34

import Definitions.Def_DeepTierFinance_Direct_Direct

namespace DeepTierFinance.Direct
noncomputable section

/-- Solving (1) for the implementing rate. Uses are certified at nonzero denominator. -/
def inverseDenominator (p : Primitives) (b y : ℝ) : ℝ :=
  deriv p.P y * (y - b) + p.P y

def inverseRate (p : Primitives) (b y : ℝ) : ℝ :=
  p.v * deriv p.P y / inverseDenominator p b y - 1

def ImplementedInverse (p : Primitives) (s : InvestmentStrategy) (b r y : ℝ) : Prop :=
  inverseDenominator p b y ≠ 0 ∧ DifferentiableAt ℝ p.P y ∧
  r = inverseRate p b y ∧ InvestmentFOC p b r y ∧
  InvestmentResponse p b r y ∧ s b r = y

/-- (EC.1), supplementing rather than defining the cash-flow optimum. -/
def BankFOC (p : Primitives) (e w b y : ℝ) : Prop :=
  DifferentiableAt ℝ p.P y ∧ DifferentiableAt ℝ (inverseRate p b) y ∧
  inverseDenominator p b y ≠ 0 ∧
  deriv p.P y * min w e + p.P y * (y - b) * deriv (inverseRate p b) y - 1 = 0

/-- (EC.2), for the target investment before taking the maximum with echelon capital. -/
def ManufacturerFOC (p : Primitives) (w r a b y : ℝ) : Prop :=
  DifferentiableAt ℝ p.P y ∧ DifferentiableAt ℝ (inverseRate p b) y ∧
  inverseDenominator p b y ≠ 0 ∧
  deriv p.P y * (w - (1 + r) * (y - a - b)) +
    p.P y * ((y - b) * deriv (inverseRate p b) y - (1 + r)) = 0

/-- Literal (EC.11)-(EC.12), with derivative existence made explicit. -/
def DelegateKKT (p : Primitives) (T : TraditionalPolicy) (D : DelegatePolicy)
    (e a b w r : ℝ) : Prop :=
  let Y := fun w r => (D.response e a b ⟨w, some r⟩).y
  let V := fun w r => delegateProfits p T e a b ⟨w, some r⟩
    (D.response e a b ⟨w, some r⟩) 1
  let y := Y w r
  let B := echelonAdvance a b y
  ∃ lam μ, 0 ≤ lam ∧ 0 ≤ μ ∧
    DifferentiableAt ℝ p.P y ∧
    DifferentiableAt ℝ (Y w) r ∧ DifferentiableAt ℝ (fun x => Y x r) w ∧
    DifferentiableAt ℝ (V w) r ∧ DifferentiableAt ℝ (fun x => V x r) w ∧
    lam * (V w r - realizedBenchmark p T e a b 1) = 0 ∧
    μ * (y - (T.response e a b (T.menu e a)).y) = 0 ∧
    (deriv p.P y * (1 - w + (1 + r) * B) + p.P y * (1 + r) - 1) *
      deriv (Y w) r + p.P y * B + lam * deriv (V w) r + μ * deriv (Y w) r = 0 ∧
    (if w < e then
      (deriv p.P y * (1 + r) * B + p.P y * (1 + r) - 1) * deriv (Y w) r +
        p.P y * B + lam * deriv (fun x => V x r) w + μ * deriv (fun x => Y x r) w = 0
     else
      (deriv p.P y * (1 + r) * B + p.P y * (1 + r) - 1) * deriv (Y w) r + p.P y * B = 0)

/-- The finite-versus-no-offer threshold in Lemma EC.1, retaining its equality convention. -/
def DelegateFinanceThreshold (p : Primitives) (c : ℝ) (R : ResponseFamily)
    (T : TraditionalPolicy) (D : DelegatePolicy) (e w b t : ℝ) : Prop :=
  ∀ a, CapitalRegion p (R e) c e a b →
    if t ≤ a then ∃ r, 0 ≤ r ∧ DelegateRateOptimal p T D e a b w (some r) ∧
      (D.response e a b ⟨w, some r⟩).financing = .manufacturer ∧
      r < ((R e).bank e w 0 b).rb ∧ DelegateKKT p T D e a b w r
    else DelegateRateOptimal p T D e a b w none ∧
      (D.response e a b ⟨w, none⟩).financing = .bank

/-- Optimality within a branch, used only when that branch has feasible adopting menus. -/
def DelegateBranch (p : Primitives) (T : TraditionalPolicy) (D : DelegatePolicy)
    (e a b : ℝ) (high : Bool) (m : BlockchainContract) : Prop :=
  DelegateFeasible p T D e a b m ∧ (if high then e ≤ m.w else m.w < e) ∧
  ∀ n, DelegateFeasible p T D e a b n → (if high then e ≤ n.w else n.w < e) →
    delegateProfits p T e a b n (D.response e a b n) 0 ≤
    delegateProfits p T e a b m (D.response e a b m) 0

end
end DeepTierFinance.Direct


