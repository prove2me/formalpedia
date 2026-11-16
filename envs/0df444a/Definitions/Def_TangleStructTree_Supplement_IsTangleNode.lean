-- Prove2me | Definitions.Def_TangleStructTree_Supplement_IsTangleNode
-- name    : TangleStructTree_Supplement_IsTangleNode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:07:37.075813+00:00
-- url     : https://prove2.me/theorems/63f37fe8-b166-4fb2-9623-6ff45103b77d
-- title:
--   Tangle nodes; a node separating two leaves
-- statement:
--   Let $T$ be a consistent separation tree on $\vec S$ and $\mathcal F$ any set. A non-leaf node $v$ is a **tangle node** if for every successor $w$ of $v$ there is a tangle leaf $\ell\ge_r w$, i.e. a leaf whose closure $\lfloor\beta_\ell\rfloor$ is an $\mathcal F$-tangle.
--
--   A node $v$ **separates** two nodes $\ell,\ell'$ if they lie above distinct children of $v$; for tangle leaves this means that $s_v$ distinguishes their tangles.
--
--   These notions describe which part of the tree structure Theorem 5.5 preserves.
--
--   **Formalization Note** "Successor" is read as *child*, as in the paper's own usage "a node of $T$ with a successor $w$, let $\vec s:=\beta(vw)$" (Lemma 5.1), where $vw$ is an edge.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §3, p.7 (PDF 18): tangle node; §5, p.15 (PDF 26): separating tangle leaves

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_SepTree
import Definitions.Def_TangleStructTree_SepTree_IsTST

namespace TangleStructTree

namespace Supplement

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- "A non-leaf node `v` is a **tangle node** if there is a tangle leaf `ℓ ≥_r w` for every successor
`w` of `v` in `>_r`" (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §3, p.7 (PDF 18)).

**Formalization Note**
1. Reading: "successor" is a child of `v`, as in the paper's own usage "Let `v` be a node of `T`
   with a successor `w`, let `s⃗ := β(vw)`" (Lemma 5.1, p.13), where `vw` is an edge.
2. Nodes are root-path label lists, newest first: the children of `v` are the nodes `x :: v`, and
   `ℓ ≥_r w` is `w <:+ ℓ`. -/
def IsTangleNode (T : SepTree E) (ℱ : Set (Set E)) (v : List E) : Prop :=
  v ∈ T.nodes ∧ (∃ x : E, x :: v ∈ T.nodes) ∧
    ∀ x : E, x :: v ∈ T.nodes → ∃ ℓ : List E, T.IsTangleLeaf ℱ ℓ ∧ (x :: v) <:+ ℓ

/-- The node `v` **separates** the nodes `ℓ` and `ℓ'` (Theorem 5.5, von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §5,
p.15 (PDF 26)): they lie above distinct children of `v`.

**Formalization Note** Nodes are root-path label lists, newest first; the children of `v` are the
lists `x :: v` and "`ℓ` lies above `x :: v`" is `(x :: v) <:+ ℓ`. This is the reading of the proof
of Theorem 5.5: "`s_v` distinguishes two tangles if and only if `v` separates their tangle leaves". -/
def Separates (v ℓ ℓ' : List E) : Prop :=
  ∃ x x' : E, x ≠ x' ∧ (x :: v) <:+ ℓ ∧ (x' :: v) <:+ ℓ'

end Supplement

end TangleStructTree


