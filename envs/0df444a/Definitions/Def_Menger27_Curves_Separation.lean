-- Prove2me | Definitions.Def_Menger27_Curves_Separation
-- name    : Menger27_Curves_Separation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:09:10.464975+00:00
-- url     : https://prove2.me/theorems/3ca1111d-68c3-44d3-a57a-28252a784fb0
-- title:
--   pp. 99–100 — separation and n-point connectedness
-- statement:
--   Let $M$ be a subspace of a topological space, and let $A,B,E\subseteq M$. The set $E$ **separates $A$ from $B$ in $M$** if $M\setminus E$ splits into disjoint sets $M_1,M_2$ closed relative to $M\setminus E$, with $A\setminus E\subseteq M_1$ and $B\setminus E\subseteq M_2$.
--
--   The space $M$ is **$n$-point connected between $A$ and $B$** when
--   $$\text{no }E\subseteq M\text{ with }|E|<n\text{ separates }A\text{ and }B.$$
--
--   The predicates are reusable for the annuli and the compact spaces in Satz β. **Formalization Note** Separators may meet $A$ or $B$. Theorems impose the paper's standing condition that $A$ and $B$ are disjoint and closed in $M$; the predicate itself records only the no-small-separator condition. Extended cardinality counts infinite $E$ correctly.
-- source:
--   Menger, Zur allgemeinen Kurventheorie, Fund. Math. 10 (1927), pp. 99–100, separation paragraph and definition of n-punktig zusammenhängend

import Mathlib

namespace Menger27.Curves

/-- Relative separation of `A` and `B` inside `M` after deleting `E`. -/
def Separates {X : Type*} [TopologicalSpace X]
    (M E A B : Set X) : Prop :=
  ∃ M₁ M₂ : Set X,
    M \ E = M₁ ∪ M₂ ∧ Disjoint M₁ M₂ ∧
    M₁ = (M \ E) ∩ closure M₁ ∧
    M₂ = (M \ E) ∩ closure M₂ ∧
    A \ E ⊆ M₁ ∧ B \ E ⊆ M₂

/-- No subset of fewer than `n` points separates `A` and `B` in `M`. -/
def NPointConnected {X : Type*} [TopologicalSpace X]
    (M A B : Set X) (n : ℕ) : Prop :=
  ∀ E : Set X, E ⊆ M → E.encard < n → ¬ Separates M E A B

end Menger27.Curves


