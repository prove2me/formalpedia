-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_NoActiveTriples
-- name    : DiscreteConvex_AlgorithmsB_NoActiveTriples
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:02:09.915247+00:00
-- url     : https://prove2.me/theorems/20d29c27-9ba9-4306-9dea-782fe9772929
-- title:
--   NoActiveTriples
-- statement:
--   No active triple exists.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.297, preceding Proposition 10.20.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.297, preceding Proposition 10.20

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_IsActiveTriple

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- No active triple exists. -/
def NoActiveTriples {ι : Type*} (I : Finset ι) (L : ι → (V ≃ Fin (Fintype.card V))) (W : Finset V) :
    Prop :=
  ∀ i u v, ¬ IsActiveTriple I L W i u v

-- ===== The IFF fixing algorithm's certificate (§10.2.3, end) =====

end DiscreteConvex.AlgorithmsB


