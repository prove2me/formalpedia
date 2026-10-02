-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_NoArcsLeaving
-- name    : DiscreteConvex_AlgorithmsB_NoArcsLeaving
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:51:15.915224+00:00
-- url     : https://prove2.me/theorems/43ea8169-b65c-4d55-8455-ec0e2a973f80
-- title:
--   NoArcsLeaving
-- statement:
--   No arc of active leaves $W$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.297, preceding Proposition 10.20.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.297, preceding Proposition 10.20

import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- No arc of `active` leaves `W`. -/
def NoArcsLeaving (active : V → V → Prop) (W : Finset V) : Prop :=
  ∀ u ∈ W, ∀ v, active u v → v ∈ W

end DiscreteConvex.AlgorithmsB


