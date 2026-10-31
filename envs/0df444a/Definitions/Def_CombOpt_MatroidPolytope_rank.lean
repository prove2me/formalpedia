-- Prove2me | Definitions.Def_CombOpt_MatroidPolytope_rank
-- name    : CombOpt_MatroidPolytope_rank
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:34.729823+00:00
-- url     : https://prove2.me/theorems/4a2748ad-60b4-4b8f-8f6f-8a247eb94652
-- title:
--   Rank function $r(A)$
-- statement:
--   For a family $\mathcal I$ of subsets of a finite set $S$ and $A\subseteq S$, let
--   $$r(A)=\max\{|J| : J\subseteq A,\ J\in\mathcal I\}.$$
--
--   For a matroid, every basis of $A$ is a largest independent subset of $A$ (by (M2) all bases of $A$ have the same size), so $r(A)$ is the size of any basis of $A$: the book's **rank** of $A$. The rank function gives the right-hand sides of the linear program (8.1) and of the matroid polytope.
--
--   **Formalization Note** The maximum is a supremum of cardinalities over the independent subsets of $A$, a natural number; it is $0$ if no subset of $A$ is independent, which (M0) rules out.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.1, p. 275 (PDF p. 282)

import Mathlib

namespace CombOpt.MatroidPolytope

open Classical in
/-- **Rank of a set.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.1, p. 275 (PDF p. 282): "A maximal independent subset of a set A ⊆ S is called a basis
of A. Its size (which depends only on A, by (M2)) is the *rank* of A, denoted r(A)."

`rank I A` is the largest cardinality of an independent subset of `A`.

**Formalization Note.** For a matroid every basis of `A` has this size: a largest independent
subset of `A` is a basis, and by (M2) all bases of `A` have the same size. So `rank I` is the
book's rank function `r` whenever `I` is a matroid; the definition itself makes sense for any
family (it is `0` when no subset of `A` is independent, which cannot happen under (M0)). -/
noncomputable def rank {α : Type*} (I : Finset α → Prop) (A : Finset α) : ℕ :=
  (A.powerset.filter I).sup Finset.card

end CombOpt.MatroidPolytope


