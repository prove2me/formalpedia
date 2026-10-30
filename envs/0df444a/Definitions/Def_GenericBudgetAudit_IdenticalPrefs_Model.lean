-- Prove2me | Definitions.Def_GenericBudgetAudit_IdenticalPrefs_Model
-- name    : GenericBudgetAudit_IdenticalPrefs_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:30:41.267444+00:00
-- url     : https://prove2.me/theorems/0984fcf7-0308-440a-b277-4e72c130691e
-- title:
--   Two-agent tie-compatible utility frontier, shares, generic budgets and pricing
-- statement:
--   For two agents and a finite set of goods, a clearing allocation assigns every good to exactly one agent. The published bundle, price, demand and competitive equilibrium helpers are reused without any bundled valuation restrictions. The new model defines nonnegative normalized additive valuations, positive normalized budgets, and efficiency as absence of a weak improvement for both agents with a strict improvement for one. Distinct efficient utility levels form a finite set.
--
--   The truncated share is the maximum efficient utility at or below the budget; the augmented share is the minimum at or above it. They return an optional real value: an empty frontier slice is recorded as absent. A fairness guarantee explicitly requires a present maximum. Optimizing allocations are characterized by attained extremum predicates. The model also defines proportionality, anti-proportionality, budget exhaustion, marginal values, the two-sided swap condition, combination pricing, equal prices on jointly identical goods, the open rectangle of Definition 6.1 and exceptional budgets of Definition 6.2.
--
--   $$
--   b_i(1-x)=(1-b_i)y,\qquad x<y\text{ consecutive distinct efficient levels of agent }i.
--   $$
--
--   This equality is the source ratio equality because both denominators are positive on normalized additive markets. The frontier uses utility-vector equality to respect identical-item interchangeability (pp. 6, 7, 13, 15). Arbitrary ties and zero-valued goods extend the source's strict-preference domain; labelled partitions and all possible affordable bundles are retained. These definitions are concrete, contain no theorem assumptions and impose neither injectivity nor uniqueness of labelled representatives.
-- source:
--   Babaioff, Nisan and Talgam-Cohen, Competitive Equilibrium with Indivisible Goods and Generic Budgets, arXiv:1703.08150v2 (2018), §2.1 and footnote 3, p. 6; Definitions 2.1 and 2.3, p. 7; Definition 4.2 and Condition (1), p. 10; Definitions 5.3–5.4, p. 13; Definitions 6.1–6.2, p. 15. https://arxiv.org/abs/1703.08150v2

import Mathlib
import Definitions.Def_GenericBudgets_AlmostEqual_Setting

open scoped Classical
open GenericBudgets.AlmostEqual (bundle price IsCE)

noncomputable section

namespace GenericBudgetAudit.IdenticalPrefs.Model

variable {m : ℕ}

/-- §2.1, p. 6: nonnegative normalized weakly monotone cardinal valuations.
The weak monotonicity and arbitrary ties are the declared generalization. -/
def IsCardinal (w : Finset (Fin m) → ℝ) : Prop :=
  (∀ S, 0 ≤ w S) ∧ w Finset.univ = 1 ∧ ∀ S T, S ⊆ T → w S ≤ w T

/-- §2.1, p. 6: normalized additive values, permitting zeros and arbitrary ties. -/
def IsAdditive (w : Finset (Fin m) → ℝ) : Prop :=
  (∀ j, 0 ≤ w {j}) ∧ (∀ S, w S = ∑ j ∈ S, w {j}) ∧ w Finset.univ = 1

/-- §2.1, p. 6: positive normalized budgets; ordering is imposed where required. -/
def IsBudgets (b : Fin 2 → ℝ) : Prop :=
  (∀ i, 0 < b i) ∧ b 0 + b 1 = 1

/-- Definition 2.3, p. 7, read on distinct utility vectors, not labelled partitions. -/
def Efficient (v : Fin 2 → Finset (Fin m) → ℝ) (σ : Fin m → Fin 2) : Prop :=
  ∀ τ : Fin m → Fin 2, (∀ i, v i (bundle σ i) ≤ v i (bundle τ i)) →
    ∀ i, v i (bundle τ i) = v i (bundle σ i)

/-- The finite set of distinct efficient utility levels of agent i. -/
def frontierLevels (v : Fin 2 → Finset (Fin m) → ℝ) (i : Fin 2) : Finset ℝ :=
  (Finset.univ.filter (Efficient v)).image (fun σ => v i (bundle σ i))

/-- Definition 5.3, p. 13: None precisely when the feasible frontier slice is empty. -/
def truncatedShare (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
    (i : Fin 2) : Option ℝ :=
  let levels := (frontierLevels v i).filter (fun x => x ≤ b i)
  if h : levels.Nonempty then some (levels.max' h) else none

/-- Definition 5.4, p. 13: None precisely when the feasible frontier slice is empty. -/
def augmentedShare (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
    (i : Fin 2) : Option ℝ :=
  let levels := (frontierLevels v i).filter (fun x => b i ≤ x)
  if h : levels.Nonempty then some (levels.min' h) else none

/-- An attained maximizing allocation of Definition 5.3, with no chosen representative. -/
def IsTruncMaximizer (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
    (i : Fin 2) (σ : Fin m → Fin 2) : Prop :=
  Efficient v σ ∧ v i (bundle σ i) ≤ b i ∧
    ∀ τ, Efficient v τ → v i (bundle τ i) ≤ b i → v i (bundle τ i) ≤ v i (bundle σ i)

/-- An attained minimizing allocation of Definition 5.4. -/
def IsAugMinimizer (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
    (i : Fin 2) (σ : Fin m → Fin 2) : Prop :=
  Efficient v σ ∧ b i ≤ v i (bundle σ i) ∧
    ∀ τ, Efficient v τ → b i ≤ v i (bundle τ i) → v i (bundle σ i) ≤ v i (bundle τ i)

/-- Getting a real, attained truncated share; an empty slice cannot certify fairness. -/
def GetsTruncatedShare (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
    (σ : Fin m → Fin 2) (i : Fin 2) : Prop :=
  ∃ x : ℝ, truncatedShare v b i = some x ∧ x ≤ v i (bundle σ i)

/-- p. 8: normalized budget proportionality for both agents. -/
def Proportional (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
    (σ : Fin m → Fin 2) : Prop :=
  ∀ i, b i ≤ v i (bundle σ i)

/-- p. 12: at most both proportional shares, with at least one strict inequality. -/
def AntiProportional (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
    (σ : Fin m → Fin 2) : Prop :=
  (∀ i, v i (bundle σ i) ≤ b i) ∧ ∃ i, v i (bundle σ i) < b i

/-- §2.2, p. 7: budget exhaustion for the given allocation and prices. -/
def Exhausting (b : Fin 2 → ℝ) (σ : Fin m → Fin 2) (p : Fin m → ℝ) : Prop :=
  ∀ i, price p (bundle σ i) = b i

/-- §4.1, p. 10: marginal values. -/
def marginal (w : Finset (Fin m) → ℝ) (A B : Finset (Fin m)) : ℝ :=
  w (A ∪ B) - w B

/-- Proposition 4.1, Condition (1), both ordered pairs and every swap. -/
def SwapCondition (v : Fin 2 → Finset (Fin m) → ℝ) (σ : Fin m → Fin 2)
    (p : Fin m → ℝ) : Prop :=
  ∀ i k : Fin 2, i ≠ k → ∀ A B : Finset (Fin m),
    A ⊆ bundle σ i → B ⊆ bundle σ k →
    marginal (v i) B (bundle σ i \ A) < marginal (v i) A (bundle σ i \ A) →
    marginal (v k) B (bundle σ k \ B) < marginal (v k) A (bundle σ k \ B) →
    price p B < price p A

/-- Definition 4.2, p. 10: nonnegative combination coefficients, at least one positive. -/
def CombinationPricing (v : Fin 2 → Finset (Fin m) → ℝ) (p : Fin m → ℝ) : Prop :=
  ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 < max α β ∧
    ∀ j, p j = α * v 0 {j} + β * v 1 {j}

/-- Footnote 3, p. 6: jointly identical singleton values have equal item prices. -/
def EqualPrices (v : Fin 2 → Finset (Fin m) → ℝ) (p : Fin m → ℝ) : Prop :=
  ∀ j k, (∀ i, v i {j} = v i {k}) → p j = p k

/-- Definition 6.1, p. 15: the open rectangle ranges over all allocations.
The frontier bounds are attained extrema, not free parameters. -/
def InRectangle (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
    (i k : Fin 2) (σ : Fin m → Fin 2) : Prop :=
  ∃ σi σk, IsTruncMaximizer v b i σi ∧ IsTruncMaximizer v b k σk ∧
    v i (bundle σi i) < v i (bundle σ i) ∧
    v i (bundle σ i) < v i (bundle σk i) ∧
    0 < v k (bundle σ k) ∧ v k (bundle σ k) < v k (bundle σk k)

/-- Definition 6.2, p. 15: consecutive distinct frontier levels, cross-multiplied.
For normalized additive valuations 0 ≤ x < y ≤ 1 makes both source denominators positive. -/
def InExceptional (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
    (i : Fin 2) : Prop :=
  ∃ x ∈ frontierLevels v i, ∃ y ∈ frontierLevels v i, x < y ∧
    (∀ z ∈ frontierLevels v i, ¬ (x < z ∧ z < y)) ∧
    b i * (1 - x) = (1 - b i) * y

end GenericBudgetAudit.IdenticalPrefs.Model


