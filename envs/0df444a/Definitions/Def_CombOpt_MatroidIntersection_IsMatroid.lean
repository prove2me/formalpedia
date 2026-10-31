-- Prove2me | Definitions.Def_CombOpt_MatroidIntersection_IsMatroid
-- name    : CombOpt_MatroidIntersection_IsMatroid
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:49.581731+00:00
-- url     : https://prove2.me/theorems/507c10cf-cc4a-46aa-a931-3de7a2a4833a
-- title:
--   Matroid axioms (M0)–(M2)
-- statement:
--   A family $\mathcal I$ of subsets of a finite set $S$ satisfies the **matroid axioms** if
--
--   1. (M0) $\emptyset\in\mathcal I$;
--   2. (M1) if $J'\subseteq J\in\mathcal I$, then $J'\in\mathcal I$;
--   3. (M2) for every $A\subseteq S$, every maximal independent subset of $A$ has the same cardinality.
--
--   Then $M=(S,\mathcal I)$ is a **matroid**. This predicate is used both to define matroids and to state that a constructed family (such as a contraction) is a matroid.
--
--   A maximal independent subset of $A$ is a **basis** of $A$, so (M2) says that all bases of $A$ have the same size.
--
--   **Formalization Note** (M2) is the published `EdmondsPartition.Main.Axiom2` (Edmonds' Axiom 2, which is the same axiom), stated with `EdmondsPartition.Main.IsMaxIndepIn` (maximal independent subset of $A$, with respect to inclusion). This is the book's axiom system, not Mathlib's `Matroid`.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.1, pp. 274–275 (PDF pp. 281–282)

import Mathlib
import Definitions.Def_EdmondsPartition_Main_Basic

namespace CombOpt.MatroidIntersection

/-- **The matroid axioms (M0)–(M2).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.1,
pp. 274–275 (PDF pp. 281–282): "Let S be a finite set and I be a family of subsets of S, called
*independent* sets. We say that M = (S, I) is a *matroid* if the following axioms are satisfied:
(M0) ∅ ∈ I. (M1) If J′ ⊆ J ∈ I, then J′ ∈ I. (M2) For every A ⊆ S, every maximal independent
subset of A has the same cardinality."
"A maximal independent subset of a set A ⊆ S is called a *basis* of A" (p. 275).

`IsMatroid Indep` says that the family `Indep` of subsets of the ground set `S` satisfies
(M0), (M1) and (M2). (M2) is the published `EdmondsPartition.Main.Axiom2`: any two maximal
independent subsets of the same set `A` (`EdmondsPartition.Main.IsMaxIndepIn Indep A J`: `J ⊆ A`,
`J` independent, and no independent `J'` with `J ⊆ J' ⊆ A` other than `J`) have the same size.

**Formalization Note.** The ground set is the whole type `S`; finiteness of `S` is imposed
where a matroid is formed (`Matroid S` requires `[Fintype S]`). This is the book's definition,
not Mathlib's `_root_.Matroid`. -/
def IsMatroid {S : Type*} [DecidableEq S] (Indep : Finset S → Prop) : Prop :=
  Indep ∅ ∧
  (∀ J' J : Finset S, J' ⊆ J → Indep J → Indep J') ∧
  EdmondsPartition.Main.Axiom2 Indep

end CombOpt.MatroidIntersection


