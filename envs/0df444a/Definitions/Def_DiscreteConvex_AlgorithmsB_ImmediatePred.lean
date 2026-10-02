-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_ImmediatePred
-- name    : DiscreteConvex_AlgorithmsB_ImmediatePred
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:50:14.898365+00:00
-- url     : https://prove2.me/theorems/437859e8-f680-4659-8680-6c0c7d9b05bb
-- title:
--   ImmediatePred
-- statement:
--   $v$ is the immediate predecessor of $u$ in $L$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.298, preceding Proposition 10.20.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.298, preceding Proposition 10.20

import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `v` is the immediate predecessor of `u` in `L`. -/
def ImmediatePred (L : V ≃ Fin (Fintype.card V)) (v u : V) : Prop := (L v).val + 1 = (L u).val

end DiscreteConvex.AlgorithmsB


