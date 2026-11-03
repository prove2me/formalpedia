-- Prove2me | Definitions.Def_BeliefDominance_DecisionSpace
-- name    : BeliefDominance_DecisionSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:24:28.131377+00:00
-- url     : https://prove2.me/theorems/b0fd368a-65ca-4145-be40-d56969305422
-- title:
--   Two-period decision spaces, optimal sets, weak consistency, fallacious and fallible inconsistency
-- statement:
--   A two-period decision has first-period actions $x_1\in X_1$. After $x_1$ a signal $y$ is observed, and the decision-maker picks a second-period action in $X_{2,x_1,y}$, which may depend on both $x_1$ and $y$. A **strategy** $x=(x_1,x_2(Y))$ consists of $x_1\in X_1$ and an action $x_2(y)\in X_{2,x_1,y}$ for each signal $y$; $X$ is the set of all strategies.
--
--   Let $\preceq$ be a relation on strategies and $\preceq_{x_1,y}$ a relation on second-period actions, with strict parts $\prec$ and $\prec_{x_1,y}$. The optimal sets are
--
--   $$
--   X^*=\{x^*\in X: x^*\not\prec x\ \ \forall x\in X\},\qquad
--   X^*_{2,x_1,y}=\{x_2^*\in X_{2,x_1,y}: x_2^*\not\prec_{x_1,y}x_2\ \ \forall x_2\in X_{2,x_1,y}\}.
--   $$
--
--   The module also defines:
--
--   1. **Weak consistency.** If $x,\tilde x\in X$, $x_1=\tilde x_1$ and $x_2(Y\ne y)=\tilde x_2(Y\ne y)$ for some $y$, then $x_2(y)\prec_{x_1,y}\tilde x_2(y)$ implies $x\prec\tilde x$, and $x_2(y)\preceq_{x_1,y}\tilde x_2(y)$ implies $x\preceq\tilde x$.
--   2. **Fallacious inconsistency.** There are $x^*\in X^*$ and $y$ with $x_2^*(y)\notin X^*_{2,x_1^*,y}$: an optimal plan prescribes a second-period action that is no longer optimal.
--   3. **Fallible inconsistency.** There are $x^*\in X^*$, $y$ and $x_2\in X^*_{2,x_1^*,y}$ such that every completion $(x_1^*,x_2,\hat x_2(Y\neq y))$ is strictly preferred by some strategy of $X$: an action becomes optimal although no optimal plan contained it.
--
--   These notions apply to any preference relation, and the mission applies them to belief dominance.
--
--   **Formalization Note** Strategies are pairs `A₁ × (Y → A₂)`, `le x x'` means $x\preceq x'$, and `le₂ x₁ y a b` means $a\preceq_{x_1,y}b$. The printed formula for fallible inconsistency leaves $x_1^*$ unbound; following the sentence before it and the proof of Theorem 4 (p. 11), it is the first-period action of some $x^*\in X^*$. The completions are encoded as the strategies $s\in X$ with $s_1=x_1^*$, $s_2(y)=x_2$.
-- source:
--   Ekholm–Baker, Multiple Beliefs, Dominance and Dynamic Consistency, Management Science, §3, p.4; §3.2, p.5; §3.3, p.6

import Mathlib

namespace BeliefDominance

/-- The decision space of a two-period problem (Ekholm–Baker, *Multiple Beliefs, Dominance and
Dynamic Consistency*, Management Science, doi:10.1287/mnsc.2020.3908, §3, p.4 (PDF p.5)):
first-period actions `X₁` and second-period actions `X₂ x₁ y = X_{2,x₁,y}`, which may depend on the
first-period action `x₁` and on the observed signal `y`.

**Formalization Note** The types `A₁`, `A₂`, `Y` of actions and signals are arbitrary. -/
structure DecisionSpace (A₁ A₂ Y : Type*) where
  /-- The first-period decision space `X₁`. -/
  X₁ : Set A₁
  /-- The second-period decision space `X_{2,x₁,y}`. -/
  X₂ : A₁ → Y → Set A₂

/-- The strategy set `X` (Ekholm–Baker, Management Science, doi:10.1287/mnsc.2020.3908, §3, p.4
(PDF p.5)): a strategy `x = (x₁, x₂(Y))` is a first-period action `x₁ ∈ X₁` with a second-period
action `x₂(y) ∈ X_{2,x₁,y}` for each signal `y`.

**Formalization Note** Strategies are pairs `A₁ × (Y → A₂)`, and `X` is the full product set. -/
def DecisionSpace.strategies {A₁ A₂ Y : Type*} (D : DecisionSpace A₁ A₂ Y) :
    Set (A₁ × (Y → A₂)) :=
  {x | x.1 ∈ D.X₁ ∧ ∀ y, x.2 y ∈ D.X₂ x.1 y}

/-- The strict part `a ≺ b` of a relation `a ≼ b` (Ekholm–Baker, Management Science,
doi:10.1287/mnsc.2020.3908, §3.2, p.5 (PDF p.6)).

**Formalization Note** `le a b` means `a ≼ b`, and `strictPart le a b` means `a ≼ b` and not
`b ≼ a`. So `x ≻ x̃` is `strictPart le x̃ x`, and `x ⊀ x̃` is `¬ strictPart le x x̃`. -/
def strictPart {α : Type*} (le : α → α → Prop) (a b : α) : Prop :=
  le a b ∧ ¬ le b a

/-- The set `X*` of a priori optimal strategies (Ekholm–Baker, Management Science,
doi:10.1287/mnsc.2020.3908, §3.2, p.5 (PDF p.6)): `x* ∈ X* ⇔ x* ⊀ x, ∀ x ∈ X`.

**Formalization Note** `le x x'` means `x ≼ x'`. -/
def optimalStrategies {A₁ A₂ Y : Type*} (D : DecisionSpace A₁ A₂ Y)
    (le : A₁ × (Y → A₂) → A₁ × (Y → A₂) → Prop) : Set (A₁ × (Y → A₂)) :=
  {xs | xs ∈ D.strategies ∧ ∀ x ∈ D.strategies, ¬ strictPart le xs x}

/-- The set `X*_{2,x₁,y}` of optimal second-period actions (Ekholm–Baker, Management Science,
doi:10.1287/mnsc.2020.3908, §3.2, p.5 (PDF p.6)):
`x₂* ∈ X*_{2,x₁,y} ⇔ x₂* ⊀_{x₁,y} x₂, ∀ x₂ ∈ X_{2,x₁,y}`.

**Formalization Note** `le₂ x₁ y a b` means `a ≼_{x₁,y} b`. -/
def optimalActions {A₁ A₂ Y : Type*} (D : DecisionSpace A₁ A₂ Y)
    (le₂ : A₁ → Y → A₂ → A₂ → Prop) (x₁ : A₁) (y : Y) : Set A₂ :=
  {a | a ∈ D.X₂ x₁ y ∧ ∀ b ∈ D.X₂ x₁ y, ¬ strictPart (le₂ x₁ y) a b}

/-- Weak consistency (Ekholm–Baker, Management Science, doi:10.1287/mnsc.2020.3908, §3.3, p.6
(PDF p.7)): if `x, x̃ ∈ X`, `x₁ = x̃₁` and `x₂(Y ≠ y) = x̃₂(Y ≠ y)` for some `y`, then
(i) `x₂(y) ≺_{x₁,y} x̃₂(y)` implies `x ≺ x̃`, and (ii) `x₂(y) ≼_{x₁,y} x̃₂(y)` implies `x ≼ x̃`.

**Formalization Note** `le x x'` means `x ≼ x'` and `le₂ x₁ y a b` means `a ≼_{x₁,y} b`; the strict
relations are `strictPart`. -/
def WeaklyConsistent {A₁ A₂ Y : Type*} (D : DecisionSpace A₁ A₂ Y)
    (le : A₁ × (Y → A₂) → A₁ × (Y → A₂) → Prop) (le₂ : A₁ → Y → A₂ → A₂ → Prop) : Prop :=
  ∀ x ∈ D.strategies, ∀ x' ∈ D.strategies, ∀ y : Y,
    x.1 = x'.1 → (∀ y' : Y, y' ≠ y → x.2 y' = x'.2 y') →
      (strictPart (le₂ x.1 y) (x.2 y) (x'.2 y) → strictPart le x x') ∧
      (le₂ x.1 y (x.2 y) (x'.2 y) → le x x')

/-- Fallacious inconsistency (Ekholm–Baker, Management Science, doi:10.1287/mnsc.2020.3908, §3.2,
p.5 (PDF p.6)): `∃ x* ∈ X*` with `x₂*(y) ∉ X*_{2,x₁*,y}` for some `y`. -/
def ExhibitsFallacious {A₁ A₂ Y : Type*} (D : DecisionSpace A₁ A₂ Y)
    (le : A₁ × (Y → A₂) → A₁ × (Y → A₂) → Prop) (le₂ : A₁ → Y → A₂ → A₂ → Prop) : Prop :=
  ∃ xs ∈ optimalStrategies D le, ∃ y : Y, xs.2 y ∉ optimalActions D le₂ xs.1 y

/-- Fallible inconsistency (Ekholm–Baker, Management Science, doi:10.1287/mnsc.2020.3908, §3.2,
p.5 (PDF p.6)): `∃ x₂ ∈ X*_{2,x₁*,y}` for some `y` such that
`∀ x̂₂(Y ≠ y) ∈ ∏_{ŷ≠y} X_{2,x₁*,ŷ} ∃ x ∈ X` so that `x ≻ (x₁*, x₂, x̂₂(Y ≠ y))`.

**Formalization Note** The printed formula leaves `x₁*` unbound; the sentence before it
("despite the first-period action being optimal") and clause (a) of the proof of Theorem 4 (p.11)
make it the first-period action of some `x* ∈ X*`. The completions
`(x₁*, x₂, x̂₂(Y ≠ y))` are exactly the strategies `s ∈ X` with `s.1 = x₁*` and `s.2 y = x₂`. -/
def ExhibitsFallible {A₁ A₂ Y : Type*} (D : DecisionSpace A₁ A₂ Y)
    (le : A₁ × (Y → A₂) → A₁ × (Y → A₂) → Prop) (le₂ : A₁ → Y → A₂ → A₂ → Prop) : Prop :=
  ∃ xs ∈ optimalStrategies D le, ∃ y : Y, ∃ a ∈ optimalActions D le₂ xs.1 y,
    ∀ s ∈ D.strategies, s.1 = xs.1 → s.2 y = a → ∃ x ∈ D.strategies, strictPart le s x

end BeliefDominance


