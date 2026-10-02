-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_PrefixUpTo
-- name    : DiscreteConvex_AlgorithmsB_PrefixUpTo
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:50:01.379989+00:00
-- url     : https://prove2.me/theorems/fbec4f48-9d82-4b71-9222-0b378b78a2e6
-- title:
--   PrefixUpTo
-- statement:
--   $V_h=\{v\in V\mid v\preceq_L v_h\}$, the prefix up to and including $v$ under $L$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.289, adjacent to Eq. (10.12).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.289, adjacent to Eq. (10.12)

import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `V_h = {v ∈ V | v ⪯_L v_h}`, the prefix up to and including `v` under `L`. -/
def PrefixUpTo (L : V ≃ Fin (Fintype.card V)) (v : V) : Finset V :=
  Finset.univ.filter (fun w => L w ≤ L v)

end DiscreteConvex.AlgorithmsB


