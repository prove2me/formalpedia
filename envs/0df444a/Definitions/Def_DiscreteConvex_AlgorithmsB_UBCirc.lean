-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_UBCirc
-- name    : DiscreteConvex_AlgorithmsB_UBCirc
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:57:43.939086+00:00
-- url     : https://prove2.me/theorems/67110d37-9923-4b4f-919e-dafa82f3ec9b
-- title:
--   UBCirc
-- statement:
--   $u^\circ_B(v)=(1/n)\ell_B(v)+(1-1/n)u_B(v)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.284.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.284

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_LB
import Definitions.Def_DiscreteConvex_AlgorithmsB_UB

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `u°_B(v) = (1/n)ℓ_B(v) + (1-1/n)u_B(v)`. -/
noncomputable def UBCirc (B : Set (V → ℤ)) (v : V) : ℚ :=
  (1/(Fintype.card V : ℚ)) * (LB B v : ℚ) + (1 - 1/(Fintype.card V : ℚ)) * (UB B v : ℚ)

end DiscreteConvex.AlgorithmsB


