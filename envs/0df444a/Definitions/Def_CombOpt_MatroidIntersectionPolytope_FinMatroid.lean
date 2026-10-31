-- Prove2me | Definitions.Def_CombOpt_MatroidIntersectionPolytope_FinMatroid
-- name    : CombOpt_MatroidIntersectionPolytope_FinMatroid
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:39:52.358236+00:00
-- url     : https://prove2.me/theorems/33343ae9-a2f8-46e8-a537-0bf3d4e4e9e6
-- title:
--   Matroid $M=(S,\mathcal I)$ (axioms (M0)–(M2))
-- statement:
--   Let $S$ be a finite set and $\mathcal I$ a family of subsets of $S$, called **independent sets**. The pair $M=(S,\mathcal I)$ is a **matroid** if
--
--   1. (M0) $\emptyset\in\mathcal I$;
--   2. (M1) if $J'\subseteq J\in\mathcal I$, then $J'\in\mathcal I$;
--   3. (M2) for every $A\subseteq S$, every maximal independent subset of $A$ has the same cardinality.
--
--   A maximal independent subset of $A$ is an independent $J\subseteq A$ that is not properly contained in any independent subset of $A$. Matroids are the set systems on which the Greedy Algorithm finds a maximum-weight independent set; every result of this mission is stated for one or two of them on a common ground set.
--
--   **Formalization Note** The ground set is a finite type and subsets are `Finset`s. This is the book's axiom system, written as a structure whose fields are the three axioms; it is not Mathlib's `Matroid`, whose ground set is a subset of a possibly infinite type.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.1, Matroid axioms (M0)–(M2), pp. 274–275 (PDF pp. 281–282)

import Mathlib

namespace CombOpt.MatroidIntersectionPolytope

/-- **Matroid** (book axioms (M0)–(M2)).
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.1, pp. 274–275 (PDF pp. 281–282): "Let S be a finite set and I be a family of subsets
of S, called independent sets. We say that M = (S, I) is a matroid if the following axioms are
satisfied: (M0) ∅ ∈ I. (M1) If J' ⊆ J ∈ I, then J' ∈ I. (M2) For every A ⊆ S, every maximal
independent subset of A has the same cardinality."

**Formalization Note.** The ground set `S` is a finite type (`[Fintype S]`) and subsets are
`Finset S`. A *maximal independent subset* of `A` (a *basis* of `A`, p. 275) is an independent
`J ⊆ A` such that no independent `J'` with `J ⊆ J' ⊆ A` differs from `J`. This is the book's own
axiom system, used instead of Mathlib's `Matroid` (whose ground set is a subset of a type);
on a finite ground set the two notions coincide. -/
structure FinMatroid (S : Type*) [Fintype S] [DecidableEq S] where
  /-- The family `I` of independent sets. -/
  Indep : Finset S → Prop
  /-- (M0) The empty set is independent. -/
  indep_empty : Indep ∅
  /-- (M1) Subsets of independent sets are independent. -/
  indep_subset : ∀ J J' : Finset S, J' ⊆ J → Indep J → Indep J'
  /-- (M2) All maximal independent subsets of a set `A` have the same cardinality. -/
  maximal_card_eq : ∀ A J₁ J₂ : Finset S,
    (J₁ ⊆ A ∧ Indep J₁ ∧ ∀ J', J₁ ⊆ J' → J' ⊆ A → Indep J' → J' = J₁) →
    (J₂ ⊆ A ∧ Indep J₂ ∧ ∀ J', J₂ ⊆ J' → J' ⊆ A → Indep J' → J' = J₂) →
    J₁.card = J₂.card

end CombOpt.MatroidIntersectionPolytope


