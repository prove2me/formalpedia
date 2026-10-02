-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_PrefixBefore
-- name    : DiscreteConvex_AlgorithmsB_PrefixBefore
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:50:07.950984+00:00
-- url     : https://prove2.me/theorems/12163b7f-9a51-4739-bc09-28e7c38be558
-- title:
--   PrefixBefore
-- statement:
--   The strict prefix before $v$ under $L$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.289, adjacent to Eq. (10.12).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.289, adjacent to Eq. (10.12)

import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The strict prefix before `v` under `L`. -/
def PrefixBefore (L : V ≃ Fin (Fintype.card V)) (v : V) : Finset V :=
  Finset.univ.filter (fun w => L w < L v)

end DiscreteConvex.AlgorithmsB


