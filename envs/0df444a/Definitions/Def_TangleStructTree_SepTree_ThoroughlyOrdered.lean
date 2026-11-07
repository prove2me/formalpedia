-- Prove2me | Definitions.Def_TangleStructTree_SepTree_ThoroughlyOrdered
-- name    : TangleStructTree_SepTree_ThoroughlyOrdered
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:54:30.813792+00:00
-- url     : https://prove2.me/theorems/a798a2a9-c074-4c32-9cb2-2186ed3947a5
-- title:
--   Thoroughly ordered separation trees
-- statement:
--   Let $T$ be a separation tree on an ordered separation system $\vec S$. $T$ is **thoroughly ordered** (in $\vec S$) if, for every non-leaf node $v$,
--
--   1. the separation $s_v$ is not oriented by $\lfloor\beta_v\rfloor$, and
--   2. $s_v$ has minimum order among the separations in $S$ not oriented by $\lfloor\beta_v\rfloor$.
--
--   A thoroughly ordered tree branches, at every node, on a separation of least order that the path so far does not already decide; for injective order functions this determines the tree.
--
--   **Formalization Note** The non-leaves are the nodes `v` with a child `x :: v`, whose labels `x` are the orientations of $s_v$; the minimum is taken over all separations of $S$ not oriented by $\lfloor\beta_v\rfloor$.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §4, p.8 (PDF 19)

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsOrientation
import Definitions.Def_TangleStructTree_sepClosure
import Definitions.Def_TangleStructTree_SepTree

namespace TangleStructTree

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- A separation tree `T` on an ordered separation system is **thoroughly ordered** (in `S⃗`) if,
for every non-leaf node `v`, the separation `s_v` is not oriented by `⌊β_v⌋` and has minimum order
among the separations in `S` not oriented by `⌊β_v⌋` (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version,
§4, p.8 (PDF 19)).

**Formalization Note** The non-leaf nodes are the `v` with a child `x :: v`; the child labels `x`
are the orientations of `s_v`, so "`s_v` is not oriented by `⌊β_v⌋`" is `¬ Orients (⌊β_v⌋) x` and
its order is `ord x`. The minimum is taken over all separations of `S` not oriented by `⌊β_v⌋`.
`ord` is the order function (see `IsOrderFunction`). -/
def SepTree.ThoroughlyOrdered (T : SepTree E) (ord : E → ℝ) : Prop :=
  ∀ (v : List E) (x : E), x :: v ∈ T.nodes →
    ¬ Orients (sepClosure (labels v)) x ∧
      ∀ y : E, ¬ Orients (sepClosure (labels v)) y → ord x ≤ ord y

end TangleStructTree


