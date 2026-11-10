-- Prove2me | Definitions.Def_RandTreeUniv_IsFourTreeDecomp
-- name    : RandTreeUniv_IsFourTreeDecomp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:10:21.070489+00:00
-- url     : https://prove2.me/theorems/2faef39c-53f3-4806-b2b8-7f66cd862059
-- title:
--   Division of a tree into four trees $T_1,\dots,T_4$ (§6)
-- statement:
--   Applying Lemma 6.1 three times with $Q=V(T)$ divides a tree $T$ into four subtrees $T_1,T_2,T_3,T_4$ with $T=T_1\cup T_2\cup T_3\cup T_4$ such that, for every $i\in\{1,2,3\}$:
--
--   1. $\min\{|V(T_i)|,\ |V(T_{i+1}\cup\dots\cup T_4)|\}\ge|V(T_i\cup\dots\cup T_4)|/3$;
--   2. $V(T_i)\cap V(T_{i+1})=\{r_{i,i+1}\}$, and for $j\ge i+2$ the trees $T_i$ and $T_j$ share a vertex if and only if $r_{i,i+1}=\dots=r_{j-1,j}$.
--
--   $T_1$, $T_3$, $T_4$ are rooted at $r_{1,2}$, $r_{2,3}$, $r_{3,4}$, and $T_2$ has the two roots $r_{1,2}$, $r_{2,3}$.
--
--   **Formalization Note** The trees are given by vertex sets $W_1,\dots,W_4$ (0-based in Lean) and $T_i$ is the subgraph of $T$ induced on $W_i$, which is required to be connected; $T=\bigcup T_i$ means every vertex and every edge of $T$ lies in some $T_i$.
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), §6, pp.30–31 (PDF 31–32)

import Mathlib

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- A division of the tree `T` into four trees `T₁, T₂, T₃, T₄` as obtained "by applying Lemma 6.1
three times with `Q = V(T)`" (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), §6, pp.30–31 (PDF 31–32)): `T = T₁ ∪ … ∪ T₄` and, for every
`i ∈ {1, 2, 3}`,
* `min{|V(T_i)|, |V(T_{i+1} ∪ … ∪ T₄)|} ≥ |V(T_i ∪ … ∪ T₄)|/3`, and
* `V(T_i) ∩ V(T_{i+1}) = {r_{i,i+1}}` and, for `j ≥ i + 2`, `T_i` and `T_j` share a vertex if
  and only if `r_{i,i+1} = … = r_{j−1,j}`.

**Formalization Note** Indices are 0-based: `W 0, …, W 3` are the vertex sets of `T₁, …, T₄`, and
`r 0, r 1, r 2` are `r_{1,2}, r_{2,3}, r_{3,4}`. Each `T_i` is the subgraph of `T` induced on
`W i`, required to be connected (a connected subgraph of a tree on a vertex set is the induced
one). `T = T₁ ∪ … ∪ T₄` is: every vertex and every edge of `T` lies in some `T_i`. -/
def IsFourTreeDecomp {V : Type*} [Fintype V] (T : SimpleGraph V) (W : Fin 4 → Finset V)
    (r : Fin 3 → V) : Prop :=
  (∀ i, (T.induce (W i : Set V)).Connected) ∧
  (∀ v, ∃ i, v ∈ W i) ∧
  (∀ u v, T.Adj u v → ∃ i, u ∈ W i ∧ v ∈ W i) ∧
  (∀ i : Fin 3,
    ((Finset.univ.filter fun j : Fin 4 => i.val ≤ j.val).biUnion W).card ≤
      3 * min (W i.castSucc).card ((Finset.univ.filter fun j : Fin 4 => i.val < j.val).biUnion W).card) ∧
  (∀ i : Fin 3, W i.castSucc ∩ W i.succ = {r i}) ∧
  (∀ i j : Fin 4, i.val + 2 ≤ j.val →
    ((W i ∩ W j).Nonempty ↔
      ∀ l l' : Fin 3, i.val ≤ l.val → l.val < j.val → i.val ≤ l'.val → l'.val < j.val → r l = r l'))

end RandTreeUniv


