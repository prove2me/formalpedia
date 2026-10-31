-- Prove2me | Definitions.Def_CombOpt_MatroidIntersection_rank
-- name    : CombOpt_MatroidIntersection_rank
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:39.987702+00:00
-- url     : https://prove2.me/theorems/dada80c7-a1f6-4a8d-ba84-7b9b8281f59d
-- title:
--   Rank function $r(A)$ of a matroid
-- statement:
--   For a matroid $M=(S,\mathcal I)$ and $A\subseteq S$, the **rank** $r(A)$ is the size of a basis (maximal independent subset) of $A$. By axiom (M2) all bases of $A$ have the same size, so $r(A)$ depends only on $A$.
--
--   The rank function enters the min–max formula of the Matroid Intersection Theorem, $\max|J| = \min\{r_1(A)+r_2(S\setminus A)\}$.
--
--   **Formalization Note** `rank Indep A` is the maximum size of a basis of $A$ (a maximal independent subset, the published `EdmondsPartition.Main.IsMaxIndepIn`) over the finite set of bases; for a matroid this is the size of any basis. It is defined for an arbitrary family so that it also gives the rank function $r'$ of a contraction before that family is known to be a matroid. On a family with no basis of $A$ (impossible for a matroid, by (M0) and finiteness) its value would be $0$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.1, p. 275 (PDF p. 282)

import Mathlib
import Definitions.Def_EdmondsPartition_Main_Basic

namespace CombOpt.MatroidIntersection

/-- **The rank function `r(A)`.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.1,
p. 275 (PDF p. 282): "A maximal independent subset of a set A ⊆ S is called a *basis* of A. Its
size (which depends only on A, by (M2)) is the *rank* of A, denoted r(A)."

`rank Indep A` is the largest size of a basis of `A` (a maximal independent subset of `A`). For a
matroid, (M2) says all bases of `A` have the same size, so this is the size of any basis of `A`;
for the rank function of a matroid `M` write `rank M.Indep`.

**Formalization Note.** The maximum is taken over the finite set of bases of `A`
(`Finset.sup` in `ℕ`); a basis of `A` is the published
`EdmondsPartition.Main.IsMaxIndepIn Indep A` (maximal independent subset of `A`). If `A` had no basis the value would be `0`; this never happens for a
matroid, where (M0) makes `∅` independent and a maximal independent subset of the finite set
`A` exists. The definition is stated for any family so that it also gives the rank function of
a family not yet known to be a matroid (Theorem 8.11). -/
noncomputable def rank {S : Type*} [DecidableEq S] (Indep : Finset S → Prop) (A : Finset S) : ℕ := by
  classical
  exact (A.powerset.filter (fun J => EdmondsPartition.Main.IsMaxIndepIn Indep A J)).sup Finset.card

end CombOpt.MatroidIntersection


