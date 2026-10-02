-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_LBCirc
-- name    : DiscreteConvex_AlgorithmsB_LBCirc
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:57:21.752683+00:00
-- url     : https://prove2.me/theorems/5be3df8d-47ec-4dab-9df1-fa7777c6e44a
-- title:
--   LBCirc
-- statement:
--   $\ell^\circ_B(v)=(1-1/n)\ell_B(v)+(1/n)u_B(v)$.
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
/-- `ℓ°_B(v) = (1-1/n)ℓ_B(v) + (1/n)u_B(v)`. -/
noncomputable def LBCirc (B : Set (V → ℤ)) (v : V) : ℚ :=
  (1 - 1/(Fintype.card V : ℚ)) * (LB B v : ℚ) + (1/(Fintype.card V : ℚ)) * (UB B v : ℚ)

end DiscreteConvex.AlgorithmsB


