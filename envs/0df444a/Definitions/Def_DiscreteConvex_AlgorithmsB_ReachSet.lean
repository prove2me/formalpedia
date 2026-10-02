-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_ReachSet
-- name    : DiscreteConvex_AlgorithmsB_ReachSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:51:26.093215+00:00
-- url     : https://prove2.me/theorems/e8380661-be2e-4faa-9ad2-84856a7832a3
-- title:
--   ReachSet
-- statement:
--   $R(u)$, the set of vertices reachable from $u$ in the digraph $(U,F)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.301, preceding Eq. (10.26).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.301, preceding Eq. (10.26)

import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `R(u)`, the set of vertices reachable from `u` in the digraph `(U,F)`. -/
noncomputable def ReachSet {U : Type*} [Fintype U] [DecidableEq U] (F : U → U → Prop) (u : U) : Finset U :=
  Finset.univ.filter (fun w => Relation.ReflTransGen F u w)

end DiscreteConvex.AlgorithmsB


