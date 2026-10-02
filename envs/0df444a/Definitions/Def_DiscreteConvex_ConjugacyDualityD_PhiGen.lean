-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_PhiGen
-- name    : DiscreteConvex_ConjugacyDualityD_PhiGen
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:58:32.389892+00:00
-- url     : https://prove2.me/theorems/d43d069c-e016-49af-b59e-da09c1067588
-- title:
--   PhiGen
-- statement:
--   The general optimal-value function $\varphi(u)=\inf_x F(x,u)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.235, Eq. (8.57).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.235, Eq. (8.57)

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ToEReal

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The general optimal value function `φ(u) = inf_x F(x,u)`, Eq. (8.57). -/
noncomputable def PhiGen (F : (V → ℤ) → (V → ℤ) → WithTop ℝ) (u : V → ℤ) : EReal :=
  sInf {t : EReal | ∃ x : V → ℤ, t = ToEReal (F x u)}

end DiscreteConvex.ConjugacyDualityD


