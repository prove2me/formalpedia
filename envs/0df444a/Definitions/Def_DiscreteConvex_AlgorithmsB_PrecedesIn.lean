-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_PrecedesIn
-- name    : DiscreteConvex_AlgorithmsB_PrecedesIn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:50:12.786445+00:00
-- url     : https://prove2.me/theorems/ee2dec34-aaf6-4b01-81ce-658e3efb24dd
-- title:
--   PrecedesIn
-- statement:
--   $u\prec_L v$: $u$ precedes $v$ in the ordering $L$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.289, Eq. (10.14).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.289, Eq. (10.14)

import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `u ≺_L v`: `u` precedes `v` in the ordering `L` (Eq. (10.14)). -/
def PrecedesIn (L : V ≃ Fin (Fintype.card V)) (u v : V) : Prop := L u < L v

end DiscreteConvex.AlgorithmsB


