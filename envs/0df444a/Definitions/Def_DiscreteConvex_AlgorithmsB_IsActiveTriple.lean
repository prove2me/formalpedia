-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_IsActiveTriple
-- name    : DiscreteConvex_AlgorithmsB_IsActiveTriple
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:58:36.598299+00:00
-- url     : https://prove2.me/theorems/55eed26e-5428-41b3-b8f6-6dbe6c766d27
-- title:
--   IsActiveTriple
-- statement:
--   $(i,u,v)$ is an active triple: $u\in W$, $v\notin W$, and $v$ immediately precedes $u$ in $L_i$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.297, preceding Proposition 10.20.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.297, preceding Proposition 10.20

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_ImmediatePred

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `(i,u,v)` is an active triple: `u∈W`, `v∉W`, and `v` immediately precedes `u` in `Lᵢ`. -/
def IsActiveTriple {ι : Type*} (I : Finset ι) (L : ι → (V ≃ Fin (Fintype.card V))) (W : Finset V)
    (i : ι) (u v : V) : Prop :=
  i ∈ I ∧ u ∈ W ∧ v ∉ W ∧ ImmediatePred (L i) v u

end DiscreteConvex.AlgorithmsB


