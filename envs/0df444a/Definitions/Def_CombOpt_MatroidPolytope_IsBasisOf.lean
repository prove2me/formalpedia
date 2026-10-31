-- Prove2me | Definitions.Def_CombOpt_MatroidPolytope_IsBasisOf
-- name    : CombOpt_MatroidPolytope_IsBasisOf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:36.227911+00:00
-- url     : https://prove2.me/theorems/833863a9-c766-41c6-add1-9924e8bdd550
-- title:
--   Basis of a set (maximal independent subset)
-- statement:
--   Let $S$ be a finite ground set and $\mathcal I$ a family of subsets of $S$, whose members are called **independent**. For $A\subseteq S$, a **basis** of $A$ is a maximal independent subset of $A$: a set $J\subseteq A$ with $J\in\mathcal I$ such that no independent set $J'$ with $J\subsetneq J'\subseteq A$ exists.
--
--   The bases of $S$ itself are called the **bases** of $(S,\mathcal I)$. Bases enter the matroid axiom (M2) and the definition of the rank function.
--
--   **Formalization Note** The ground set is a type `α`, subsets are `Finset α`, and the family is a predicate `I : Finset α → Prop`. Maximality is stated as: every independent `J'` with `J ⊆ J' ⊆ A` equals `J`.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.1, p. 275 (PDF p. 282)

import Mathlib

namespace CombOpt.MatroidPolytope

/-- **Basis of a set.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.1, p. 275 (PDF p. 282): "A maximal independent subset of a set A ⊆ S is called a
*basis* of A."

For a family `I` of subsets of the ground set `α` (the independent sets, `I J` meaning
`J ∈ I`), `IsBasisOf I A J` says that `J` is a subset of `A`, is independent, and no
independent subset of `A` strictly contains it. The bases of `S` (`A = Finset.univ`) are the
*bases of M*.

**Formalization Note.** The ground set `S` is the type `α`; subsets are `Finset`s. -/
def IsBasisOf {α : Type*} (I : Finset α → Prop) (A J : Finset α) : Prop :=
  J ⊆ A ∧ I J ∧ ∀ J' : Finset α, J ⊆ J' → J' ⊆ A → I J' → J' = J

end CombOpt.MatroidPolytope


