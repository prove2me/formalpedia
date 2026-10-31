-- Prove2me | Definitions.Def_CombOpt_MatroidPolytope_IsMatroid
-- name    : CombOpt_MatroidPolytope_IsMatroid
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:07:27.430001+00:00
-- url     : https://prove2.me/theorems/555db0d2-4b7d-42da-a25c-72b4b3e0ab3a
-- title:
--   Matroid (axioms M0, M1, M2)
-- statement:
--   Let $S$ be a finite set and $\mathcal I$ a family of subsets of $S$, called independent sets. The pair $M=(S,\mathcal I)$ is a **matroid** if
--
--   1. (M0) $\emptyset\in\mathcal I$;
--   2. (M1) if $J'\subseteq J\in\mathcal I$, then $J'\in\mathcal I$;
--   3. (M2) for every $A\subseteq S$, every maximal independent subset of $A$ has the same cardinality.
--
--   A pair satisfying (M0) and (M1) only is an **independence system**. Matroids are exactly the independence systems on which the Greedy Algorithm is optimal for every weighting; their independent sets have a polyhedral description through the rank function.
--
--   **Formalization Note** (M0) and (M1) are the published definition `SubsamplingSM.Offline.IsIndepSystem` (same two axioms on a predicate `I : Finset α → Prop`). (M2) is stated as: any two bases of the same set $A$ have the same cardinality. This is the book's definition, not Mathlib's `Matroid`.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.1, pp. 274–275 (PDF pp. 281–282), axioms (M0), (M1), (M2)

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsIndepSystem
import Definitions.Def_CombOpt_MatroidPolytope_IsBasisOf

namespace CombOpt.MatroidPolytope

/-- **Matroid (axioms M0–M2).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.1, pp. 274–275 (PDF pp. 281–282): "Let S be a finite set and I be a family of subsets
of S, called independent sets. We say that M = (S, I) is a matroid if the following axioms are
satisfied: (M0) ∅ ∈ I. (M1) If J′ ⊆ J ∈ I, then J′ ∈ I. (M2) For every A ⊆ S, every maximal
independent subset of A has the same cardinality."

(M0) and (M1) together are the published `SubsamplingSM.Offline.IsIndepSystem` (an
*independence system*, p. 277); (M2) says that any two bases of the same set `A` have the same
size.

**Formalization Note.** The ground set `S` is the type `α` (finite where a statement needs it,
through `[Fintype α]`); the family `I` is a predicate on `Finset α`. This is the book's
definition verbatim, not Mathlib's `Matroid` (which, for a finite ground set equal to the whole
type, is equivalent). -/
def IsMatroid {α : Type*} (I : Finset α → Prop) : Prop :=
  SubsamplingSM.Offline.IsIndepSystem I ∧
    ∀ A J₁ J₂ : Finset α, IsBasisOf I A J₁ → IsBasisOf I A J₂ → J₁.card = J₂.card

end CombOpt.MatroidPolytope


