-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_ReachSet
-- name    : DiscreteConvex_AlgorithmsC_ReachSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:17:41.197336+00:00
-- url     : https://prove2.me/theorems/978aeefa-2385-423b-800b-89b33d8883d7
-- title:
--   ReachSet
-- statement:
--   $R(u)$, the set of vertices reachable from $u$ in the digraph $(U,F)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.301, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.301, redeclared

import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `R(u)`, the set of vertices reachable from `u` in the digraph `(U,F)`. -/
noncomputable def ReachSet {U : Type*} [Fintype U] [DecidableEq U] (F : U → U → Prop) (u : U) :
    Finset U :=
  Finset.univ.filter (fun w => Relation.ReflTransGen F u w)

end DiscreteConvex.AlgorithmsC


