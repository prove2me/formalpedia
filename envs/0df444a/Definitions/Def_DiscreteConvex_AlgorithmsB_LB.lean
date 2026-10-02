-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_LB
-- name    : DiscreteConvex_AlgorithmsB_LB
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:49:58.407004+00:00
-- url     : https://prove2.me/theorems/1426c398-7229-4455-b47e-bedf86c33fde
-- title:
--   LB
-- statement:
--   $\ell_B(v)=\min_{y\in B}y(v)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.284, preceding Eq. (10.3).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.284, preceding Eq. (10.3)

import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `ℓ_B(v) = min_{y∈B} y(v)`. -/
noncomputable def LB (B : Set (V → ℤ)) (v : V) : ℤ := sInf ((fun y : V → ℤ => y v) '' B)

end DiscreteConvex.AlgorithmsB


