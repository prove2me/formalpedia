-- Prove2me | Definitions.Def_DeepTierFinance_Direct_Primitives
-- name    : DeepTierFinance_Direct_Primitives
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:20:41.565991+00:00
-- url     : https://prove2.me/theorems/5a695741-b74c-49a0-8ce2-d5d81795a1b2
-- title:
--   Reliability, unconstrained investment, and tier-2 best responses
-- statement:
--   The primitives are a positive procurement price v<1 and a real reliability function P whose values on nonnegative investment lie in [0,1), which is nondecreasing and concave there. Emergency cost satisfies v<e<1. CapitalOptimum records the unique global maximizer c of vP(y)-y on y≥0 and the source's characterization vP′(c)=1; its existence is asserted by the theorems, not assumed of P. Tier-2 terminal cash is P(y)v+θ₂-y for self-funding and P(y)[v-(1+r)(y-θ₂)]⁺ when borrowing. The advance is (y-θ₂)⁺. An implemented investment maximizes this cash over every nonnegative real investment and covers the outside option θ₂. The published general sequential-game best-response predicate supplies this maximization. InvestmentFOC expresses (1) with derivative existence. Complete response functions carry data only, and rationality is a separate predicate. No optimum is selected from an empty feasible set.
-- source:
--   Dong, Qiu and Xu (2022), Blockchain-Enabled Deep-Tier Supply Chain Finance, MSOM forthcoming, supplied May 2022 manuscript, DOI 10.1287/msom.2022.1123 (published citation basis), Sections 3–4.1, printed/PDF pp. 7–10

import Mathlib
import Definitions.Def_CollabProject_TimeDep_Game

namespace DeepTierFinance.Direct

noncomputable section

/-- Exogenous procurement price and reliability technology; no optimality conclusions. -/
structure Primitives where
  v : ℝ
  P : ℝ → ℝ

/-- Section 3's real, increasing concave reliability technology. -/
def Primitives.Valid (p : Primitives) : Prop :=
  0 < p.v ∧ p.v < 1 ∧
  (∀ y, 0 ≤ y → 0 ≤ p.P y ∧ p.P y < 1) ∧
  MonotoneOn p.P (Set.Ici 0) ∧ ConcaveOn ℝ (Set.Ici 0) p.P

/-- Emergency procurement cost, strictly between the two ordinary prices. -/
def EmergencyCost (p : Primitives) (e : ℝ) : Prop := p.v < e ∧ e < 1

/-- The source's unconstrained investment optimization, including uniqueness. -/
def CapitalOptimum (p : Primitives) (c : ℝ) : Prop :=
  0 ≤ c ∧ (∀ y, 0 ≤ y → p.v * p.P y - y ≤ p.v * p.P c - c) ∧
  (∀ y, 0 ≤ y → p.v * p.P y - y = p.v * p.P c - c → y = c) ∧
  HasDerivAt p.P (1 / p.v) c

/-- Positive part and the direct/tier-1 advance, respectively. -/
def positivePart (x : ℝ) : ℝ := max x 0

def advance (θ y : ℝ) : ℝ := positivePart (y - θ)

/-- Terminal cash from self-funding or borrowing; initial capital is not profit. -/
def supplierCash (p : Primitives) (θ r y : ℝ) : ℝ :=
  if y ≤ θ then p.P y * p.v + θ - y
  else p.P y * positivePart (p.v - (1 + r) * (y - θ))

/-- The investment follower of a financing offer, using the published general game. -/
def investmentGame (p : Primitives) (θ : ℝ) :
    CollabProject.TimeDep.SequentialGame NNReal NNReal where
  payoff1 r y := p.P y * ((1 + (r : ℝ)) * advance θ y)
  payoff0 r y := supplierCash p θ r y

/-- A best response also permits rejecting trade and retaining initial capital. -/
def InvestmentResponse (p : Primitives) (θ r y : ℝ) : Prop :=
  ∃ hr : 0 ≤ r, ∃ hy : 0 ≤ y, θ ≤ supplierCash p θ r y ∧
    CollabProject.TimeDep.SequentialGame.IsBR0 (investmentGame p θ).payoff0
      ⟨r, hr⟩ ⟨y, hy⟩

/-- Equation (1); the derivative exists, rather than using deriv's junk value. -/
def InvestmentFOC (p : Primitives) (θ r z : ℝ) : Prop :=
  ∃ d, HasDerivAt p.P d z ∧
    d * (p.v - (1 + r) * (z - θ)) - p.P z * (1 + r) = 0

/-- A complete investment response strategy. Its rationality is a separate predicate. -/
abbrev InvestmentStrategy := ℝ → ℝ → ℝ

def InvestmentRational (p : Primitives) (c : ℝ) (s : InvestmentStrategy) : Prop :=
  ∀ θ ∈ Set.Icc 0 c, ∀ r, 0 ≤ r → InvestmentResponse p θ r (s θ r)

end
end DeepTierFinance.Direct


