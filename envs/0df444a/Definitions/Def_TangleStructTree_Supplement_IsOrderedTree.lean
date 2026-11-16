-- Prove2me | Definitions.Def_TangleStructTree_Supplement_IsOrderedTree
-- name    : TangleStructTree_Supplement_IsOrderedTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:05:56.176111+00:00
-- url     : https://prove2.me/theorems/263df64d-8f5b-4729-9b7a-e2856aa07d1d
-- title:
--   Ordered separation trees
-- statement:
--   A separation tree $(T,r,\beta)$ on an ordered separation system $\vec S$ is **ordered** if
--
--   $$|s_v|\le|s_w|\quad\text{whenever } v,w \text{ are non-leaves of } T \text{ with } v\le_r w,$$
--
--   where $s_v$ is the separation whose two orientations label the edges from $v$ to its children and $\le_r$ is the tree order (ancestor relation) of the rooted tree.
--
--   Ordered trees put lower-order separations closer to the root; they are one of the three properties of the trees produced by Theorem 6.1.
--
--   **Formalization Note** Nodes are recorded by their root-path label lists, newest label first, so $v\le_r w$ is "$v$ is a suffix of $w$", and the order of $s_v$ is the order of any child label $x$ of $v$.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §4, p.8 (PDF 19): ordered separation tree

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_SepTree

namespace TangleStructTree

namespace Supplement

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- A separation tree `T` on an ordered separation system is **ordered** if `|s_v| ≤ |s_w|`
whenever `v` and `w` are non-leaves of `T` with `v ≤_r w` (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §4, p.8 (PDF 19)).

**Formalization Note**
1. Nodes are root-path label lists, newest label first (see `SepTree`), so `v ≤_r w` is
   `v <:+ w` (`v` is a suffix of `w`).
2. `v` is a non-leaf iff some `x :: v` is a node, and then `x` is an orientation of `s_v`, so
   `|s_v| = ord x` for the order function `ord` (`IsOrderFunction ord`: `ord (x∗) = ord x`). -/
def IsOrderedTree (T : SepTree E) (ord : E → ℝ) : Prop :=
  ∀ (v w : List E) (x y : E), x :: v ∈ T.nodes → y :: w ∈ T.nodes → v <:+ w → ord x ≤ ord y

end Supplement

end TangleStructTree


