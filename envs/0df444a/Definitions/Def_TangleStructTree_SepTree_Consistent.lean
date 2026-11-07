-- Prove2me | Definitions.Def_TangleStructTree_SepTree_Consistent
-- name    : TangleStructTree_SepTree_Consistent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:53:14.375272+00:00
-- url     : https://prove2.me/theorems/c43e94aa-4649-47aa-91a7-c820e1ee85bc
-- title:
--   Consistent separation trees
-- statement:
--   A separation tree $(T,r,\beta)$ on $\vec S$ is **consistent** if the label set $\beta_v\subseteq\vec S$ is consistent for every node $v$ of $T$.
--
--   Consistent separation trees store consistent partial orientations along their paths; tangle structure trees are consistent by definition.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §3, p.6 (PDF 17)

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsConsistent
import Definitions.Def_TangleStructTree_SepTree

namespace TangleStructTree

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- A separation tree `T` is **consistent** if `β_v ⊆ S⃗` is consistent for every node `v ∈ T`
(von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §3, p.6 (PDF 17)). -/
def SepTree.Consistent (T : SepTree E) : Prop :=
  ∀ v ∈ T.nodes, IsConsistent (labels v)

end TangleStructTree


