-- Prove2me | Definitions.Def_DeepTierFinance_Direct_Traditional
-- name    : DeepTierFinance_Direct_Traditional
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:22:19.324552+00:00
-- url     : https://prove2.me/theorems/7cb1e1ef-6f22-4892-9ba1-e46638883600
-- title:
--   Traditional equilibrium under an arbitrary capital prior
-- statement:
--   The prior is any Borel probability measure assigning mass one to [0,c), including atomic measures. A response family supplies the sequential supplier actions for each emergency cost. CoreValid certifies the constructed capital optimum, supplier responses, and source-asserted positivity of the auxiliary capital bound; it occurs in theorem conclusions. TraditionalPolicy provides a contract and complete continuation. A traditional optimum is an admissible contract maximizing the integral of the realized Table 1 manufacturer payoff over this prior. Integrability is explicitly required for the objective and every competing contract, preventing Lean's default integral from acting as a payoff. The price domain is underline-w≤w≤1, rates are nonnegative, and the stated total-capital constraint is retained. Branch optima maximize the same objective on w<e or w≥e. TraditionalThreshold characterizes the global optimum across emergency costs: the high-price branch has w=e, including equality at the threshold. Realized benchmark profits subtract supplier initial capital; adoption never compares to the manufacturer's ex ante average.
-- source:
--   Dong, Qiu and Xu (2022), Blockchain-Enabled Deep-Tier Supply Chain Finance, MSOM forthcoming, supplied May 2022 manuscript, DOI 10.1287/msom.2022.1123 (published citation basis), Section 4.3, printed/PDF pp. 13–14, equations (4)–(6)

import Definitions.Def_DeepTierFinance_Direct_Lending

namespace DeepTierFinance.Direct
open MeasureTheory
noncomputable section

/-- Response systems indexed by the exogenous emergency cost, not by the prior. -/
abbrev ResponseFamily := ℝ → Responses

def CoreValid (p : Primitives) (c : ℝ) (R : ResponseFamily) : Prop :=
  CapitalOptimum p c ∧ ∀ e, EmergencyCost p e →
    ResponsesRational p (R e) c e ∧ 0 < capitalUpper p (R e) c e ∧
    p.v < wholesaleLower p (R e) c e

def Prior (μ : Measure ℝ) (c : ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ μ (Set.Ico 0 c) = 1

/-- The contract domain, including the total-capital constraint used in Section 4. -/
def TraditionalFeasible (p : Primitives) (s : Responses) (c e a : ℝ) (m : Contract) : Prop :=
  wholesaleLower p s c e ≤ m.w ∧ m.w ≤ 1 ∧ 0 ≤ m.r ∧
  ∀ b ∈ Set.Ico 0 c, a + b ≤ bankInvestment s e m.w 0 c

/-- Complete continuation after every manufacturer's contract, and its selected optimum. -/
structure TraditionalPolicy where
  response : ℝ → ℝ → ℝ → Contract → Outcome
  menu : ℝ → ℝ → Contract

def realizedBenchmark (p : Primitives) (T : TraditionalPolicy) (e a b : ℝ) : Profits :=
  traditionalProfits p e a b (T.menu e a) (T.response e a b (T.menu e a))

def traditionalValue (p : Primitives) (μ : Measure ℝ) (T : TraditionalPolicy)
    (e a : ℝ) (m : Contract) : ℝ :=
  ∫ b, traditionalProfits p e a b m (T.response e a b m) 0 ∂μ

/-- Genuine expected-payoff maximization, with complete rational continuation. -/
def TraditionalOptimal (p : Primitives) (s : Responses) (c : ℝ) (μ : Measure ℝ)
    (T : TraditionalPolicy) (e a : ℝ) (m : Contract) : Prop :=
  TraditionalFeasible p s c e a m ∧
  (∀ n, TraditionalFeasible p s c e a n →
    (∀ b ∈ Set.Ico 0 c, TraditionalResponse p s e a b n (T.response e a b n)) ∧
    Integrable (fun b => traditionalProfits p e a b n (T.response e a b n) 0) μ ∧
    traditionalValue p μ T e a n ≤ traditionalValue p μ T e a m)

def TraditionalEquilibrium (p : Primitives) (c : ℝ) (μ : Measure ℝ)
    (R : ResponseFamily) (T : TraditionalPolicy) : Prop :=
  ∀ e, EmergencyCost p e → ∀ a ∈ Set.Icc 0 (capitalUpper p (R e) c e),
    TraditionalOptimal p (R e) c μ T e a (T.menu e a)

/-- Regime-specific optima are optimizers of the original objective on the price branch. -/
def TraditionalRegimeOptimal (p : Primitives) (s : Responses) (c : ℝ) (μ : Measure ℝ)
    (T : TraditionalPolicy) (e a : ℝ) (high : Bool) (m : Contract) : Prop :=
  TraditionalFeasible p s c e a m ∧ (if high then e ≤ m.w else m.w < e) ∧
  ∀ n, TraditionalFeasible p s c e a n → (if high then e ≤ n.w else n.w < e) →
    traditionalValue p μ T e a n ≤ traditionalValue p μ T e a m

/-- The emergency-cost crossing is specified by actual global and branch optima. -/
def TraditionalThreshold (p : Primitives) (c : ℝ) (μ : Measure ℝ)
    (R : ResponseFamily) (T : TraditionalPolicy) (a t : ℝ) : Prop :=
  ∀ e, EmergencyCost p e → a ∈ Set.Icc 0 (capitalUpper p (R e) c e) →
    TraditionalOptimal p (R e) c μ T e a (T.menu e a) ∧
    (if e ≤ t then (T.menu e a).w = e ∧
      TraditionalRegimeOptimal p (R e) c μ T e a true (T.menu e a)
     else (T.menu e a).w < e ∧
      TraditionalRegimeOptimal p (R e) c μ T e a false (T.menu e a))

end
end DeepTierFinance.Direct


