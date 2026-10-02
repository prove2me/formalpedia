-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsEmbedOf
-- name    : DiscreteConvex_ConjugacyDualityD_IsEmbedOf
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:58:32.650193+00:00
-- url     : https://prove2.me/theorems/9fb9a848-e558-4f4d-bf1a-ec55c74d9df7
-- title:
--   IsEmbedOf
-- statement:
--   $F$ embeds a `WithTop ℝ`-valued function satisfying $P$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.240, formalization device.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.240, formalization device

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ToEReal

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `F` embeds a `WithTop ℝ`-valued function satisfying `P`. -/
def IsEmbedOf (P : ((V → ℤ) → WithTop ℝ) → Prop) (F : (V → ℤ) → EReal) : Prop :=
  ∃ h : (V → ℤ) → WithTop ℝ, P h ∧ ∀ x, F x = ToEReal (h x)

end DiscreteConvex.ConjugacyDualityD


