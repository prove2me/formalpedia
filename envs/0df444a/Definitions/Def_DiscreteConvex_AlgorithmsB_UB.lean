-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_UB
-- name    : DiscreteConvex_AlgorithmsB_UB
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:49:42.868838+00:00
-- url     : https://prove2.me/theorems/4b0e32a2-3900-4ffb-9ab3-88a81f8540c6
-- title:
--   UB
-- statement:
--   $u_B(v)=\max_{y\in B}y(v)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.284, preceding Eq. (10.3).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.284, preceding Eq. (10.3)

import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `u_B(v) = max_{y∈B} y(v)`. -/
noncomputable def UB (B : Set (V → ℤ)) (v : V) : ℤ := sSup ((fun y : V → ℤ => y v) '' B)

end DiscreteConvex.AlgorithmsB


