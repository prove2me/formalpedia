-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_KGen
-- name    : DiscreteConvex_ConjugacyDualityD_KGen
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:58:25.962676+00:00
-- url     : https://prove2.me/theorems/dc8a2d7a-65dc-4e1d-a3f4-557cc722c6f8
-- title:
--   KGen
-- statement:
--   The general Lagrangian function $K(x,y)=\inf_u[F(x,u)+\langle u,y\rangle]$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.235, Eq. (8.58).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.235, Eq. (8.58)

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ToEReal

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The general Lagrangian function `K(x,y) = inf_u [F(x,u) + ⟨u,y⟩]`, Eq. (8.58). -/
noncomputable def KGen (F : (V → ℤ) → (V → ℤ) → WithTop ℝ) (x y : V → ℤ) : EReal :=
  sInf {t : EReal | ∃ u : V → ℤ, t = ToEReal (F x u) + ((∑ i, (u i : ℝ) * (y i : ℝ) : ℝ) : EReal)}

end DiscreteConvex.ConjugacyDualityD


