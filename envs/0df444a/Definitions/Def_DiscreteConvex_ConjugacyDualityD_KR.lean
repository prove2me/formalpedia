-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_KR
-- name    : DiscreteConvex_ConjugacyDualityD_KR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:00:33.993533+00:00
-- url     : https://prove2.me/theorems/4bad6a03-48a2-459b-9ceb-34fb0c447118
-- title:
--   KR
-- statement:
--   The $r$-regularized Lagrangian function $K_r(x,y)=\inf_u[F_r(x,u)+\langle u,y\rangle]$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.236, Eq. (8.64).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.236, Eq. (8.64)

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ToEReal
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_Fr

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The `r`-regularized Lagrangian function `Kr(x,y) = inf_u [Fr(x,u)+⟨u,y⟩]`, Eq. (8.64). -/
noncomputable def KR (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ)) (x y : V → ℤ) : EReal :=
  sInf {t : EReal | ∃ u : V → ℤ,
    t = ToEReal (Fr c r B x u) + ((∑ i, (u i : ℝ) * (y i : ℝ) : ℝ) : EReal)}

end DiscreteConvex.ConjugacyDualityD


