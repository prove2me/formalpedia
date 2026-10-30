-- Prove2me | Definitions.Def_SimchiLeviAddOn_Learning_Model
-- name    : SimchiLeviAddOn_Learning_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:57:41.271186+00:00
-- url     : https://prove2.me/theorems/4bb1c69b-d954-41d2-9f7b-887dc4aaaef2
-- title:
--   Finite-menu add-on model, revenue, literal subproblem and scales
-- statement:
--   Positive numbers N and M count core and supportive products. Three finite nonempty nonnegative real price menus have arbitrary values, and S is any nonnegative integer. Four arbitrary demand tables take values in [0,1]. A policy gives core prices, supportive original and discount prices, and discount selections. Equation (1) requires at most S selections and discount < original for every supportive product, including unselected products. Revenue is core primary revenue plus supportive primary revenue plus expected core purchases times conditional supportive revenue. The benchmark is the attained maximum over feasible policies. The separate literal subproblem uses equation (3)'s reversed inequality. The price scale uses only core and original prices. U is the largest menu cardinality. Lambda minimizes the probability of nonzero total primary demand over feasible policies, including supportive primary purchases. A zero lambda gives an infinite upper bound. No monotonicity, inventory or positive core-arrival assumption is imposed.
-- source:
--   Simchi-Levi, Sun and Zhang, arXiv:2005.00947v1 (2 May 2020), https://arxiv.org/abs/2005.00947v1, Sections 2-4, pp. 7-11 and 16 (same PDF pages), equations (1), (3), (7)

import Mathlib

open scoped BigOperators ENNReal

namespace SimchiLeviAddOn.Learning

/-- Finite nonnegative real menus, with distinct labels, and positive product counts.
No demand model or feasibility condition is bundled into the menu data. -/
structure Market where
  N : ℕ
  M : ℕ
  nc : ℕ
  ns : ℕ
  na : ℕ
  S : ℕ
  hN : 0 < N
  hM : 0 < M
  hc : 0 < nc
  hs : 0 < ns
  ha : 0 < na
  core : Fin nc → ℝ
  original : Fin ns → ℝ
  discount : Fin na → ℝ
  core_nonneg : ∀ p, 0 ≤ core p
  original_nonneg : ∀ p, 0 ≤ original p
  discount_nonneg : ∀ p, 0 ≤ discount p
  core_injective : Function.Injective core
  original_injective : Function.Injective original
  discount_injective : Function.Injective discount

/-- The four independently learned parameter-price families. -/
inductive Parameter (X : Market)
  | core : Fin X.N → Fin X.nc → Parameter X
  | primary : Fin X.M → Fin X.ns → Parameter X
  | discounted : Fin X.M → Fin X.na → Parameter X
  | ordinary : Fin X.M → Fin X.ns → Parameter X
  deriving DecidableEq, Fintype

abbrev Tables (X : Market) := Parameter X → ℝ

def IsDemand (X : Market) (d : Tables X) : Prop := ∀ k, d k ∈ Set.Icc 0 1

/-- Menu tuples, including tuples that fail the unconditional strict discount constraint. -/
structure Policy (X : Market) where
  core : Fin X.N → Fin X.nc
  original : Fin X.M → Fin X.ns
  discount : Fin X.M → Fin X.na
  selected : Fin X.M → Bool
  deriving DecidableEq, Fintype

noncomputable instance (X : Market) : Nonempty (Policy X) :=
  ⟨⟨fun _ => ⟨0, X.hc⟩, fun _ => ⟨0, X.hs⟩, fun _ => ⟨0, X.ha⟩, fun _ => false⟩⟩

def selectedCount {X : Market} (p : Policy X) : ℕ :=
  ∑ m, if p.selected m then 1 else 0

def Feasible (X : Market) (p : Policy X) : Prop :=
  selectedCount p ≤ X.S ∧ ∀ m, X.discount (p.discount m) < X.original (p.original m)

def Operational (X : Market) : Prop := ∃ p : Policy X, Feasible X p

/-- Literal equation (3), whose inequality is reversed relative to equation (1). -/
def PrintedFeasible (X : Market) (p : Policy X) : Prop :=
  selectedCount p ≤ X.S ∧ ∀ m, X.original (p.original m) < X.discount (p.discount m)

noncomputable def coreDemand (X : Market) (d : Tables X) (p : Policy X) : ℝ :=
  ∑ n, d (.core n (p.core n))

noncomputable def primarySupport (X : Market) (d : Tables X) (p : Policy X) : ℝ :=
  ∑ m, d (.primary m (p.original m)) * X.original (p.original m)

noncomputable def addonSupport (X : Market) (d : Tables X) (p : Policy X) : ℝ :=
  ∑ m, if p.selected m then
    d (.discounted m (p.discount m)) * X.discount (p.discount m)
    else d (.ordinary m (p.original m)) * X.original (p.original m)

noncomputable def revenue (X : Market) (d : Tables X) (p : Policy X) : ℝ :=
  (∑ n, d (.core n (p.core n)) * X.core (p.core n)) + primarySupport X d p +
    coreDemand X d p * addonSupport X d p

/-- A maximum over the finite feasible set; Operational supplies nonemptiness. -/
noncomputable def optimum (X : Market) (d : Tables X) : ℝ :=
  sSup {v | ∃ p : Policy X, Feasible X p ∧ v = revenue X d p}

/-- Used only on the nonempty literal equation (3) domain, separately from Operational. -/
noncomputable def printedSupportiveValue (X : Market) (d : Tables X) (γ : ℝ) : ℝ :=
  sSup {v | ∃ p : Policy X, PrintedFeasible X p ∧
    v = primarySupport X d p + γ * addonSupport X d p}

noncomputable def priceScale (X : Market) : ℝ :=
  max (sSup (Set.range X.core)) (sSup (Set.range X.original))

def menuScale (X : Market) : ℕ := max X.nc (max X.ns X.na)

/-- Probability of at least one primary purchase, including primary supportive demand. -/
noncomputable def primaryArrival (X : Market) (d : Tables X) (p : Policy X) : ℝ :=
  1 - (∏ n, (1 - d (.core n (p.core n)))) *
    (∏ m, (1 - d (.primary m (p.original m))))

noncomputable def arrivalFloor (X : Market) (d : Tables X) : ℝ :=
  sInf {v | ∃ p : Policy X, Feasible X p ∧ v = primaryArrival X d p}

/-- Extended nonnegative bound; a zero arrival floor gives infinity, including at T=1. -/
noncomputable def regretScale (X : Market) (d : Tables X) (ε : ℝ) (T : ℕ) : ℝ≥0∞ :=
  if arrivalFloor X d = 0 then ⊤ else
    ENNReal.ofReal ((X.N : ℝ) * X.M * priceScale X *
      ((1 / arrivalFloor X d) * Real.sqrt ((menuScale X : ℝ) * T * Real.log T) +
        ε * Real.sqrt T))

end SimchiLeviAddOn.Learning


