-- Prove2me | Definitions.Def_CombOpt_MatroidIntersectionPolytope_rank
-- name    : CombOpt_MatroidIntersectionPolytope_rank
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:36.408533+00:00
-- url     : https://prove2.me/theorems/f50f41e9-74d7-4914-8614-b2ccb71a48aa
-- title:
--   Rank function $r(A)$ of a matroid
-- statement:
--   For a matroid $M=(S,\mathcal I)$ and $A\subseteq S$, a maximal independent subset of $A$ is a **basis** of $A$, and its size, which by (M2) does not depend on the basis, is the **rank** of $A$:
--
--   $$
--   r(A)=\max\{|J| : J\subseteq A,\ J\in\mathcal I\}.
--   $$
--
--   The rank function gives the right-hand sides of the matroid polytope system (8.1) and the matroid intersection system (8.7).
--
--   **Formalization Note** The value is a natural number, computed as the largest cardinality of an independent subset of $A$; the family contains $\emptyset$, so the maximum is genuine.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.1, p. 275 (PDF p. 282), definition of basis and rank

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_FinMatroid

namespace CombOpt.MatroidIntersectionPolytope

/-- **Rank function** `r(A)` of a matroid.
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.1, p. 275 (PDF p. 282): "A maximal independent subset of a set A ⊆ S is called a basis
of A. Its size (which depends only on A, by (M2)) is the rank of A, denoted r(A)."

`rank M A` is the largest cardinality of an independent subset of `A`.

**Formalization Note.** The value is a natural number. A largest independent subset of `A` is a
maximal one, so by (M2) this maximum is the size of every basis of `A`, which is the book's
definition. The family over which the maximum is taken contains `∅` by (M0), so it is a genuine
maximum (no junk value). -/
noncomputable def rank {S : Type*} [Fintype S] [DecidableEq S] (M : FinMatroid S)
    (A : Finset S) : ℕ :=
  open Classical in (A.powerset.filter M.Indep).sup Finset.card

end CombOpt.MatroidIntersectionPolytope


