-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsNegOf
-- name    : DiscreteConvex_ConjugacyDualityD_IsNegOf
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:58:46.095264+00:00
-- url     : https://prove2.me/theorems/f3c06ed4-3754-429d-b8ae-9a1245dfee54
-- title:
--   IsNegOf
-- statement:
--   $F$ is the negation of a `WithTop ℝ`-valued function satisfying $P$.
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
/-- `F` is the negation of a `WithTop ℝ`-valued function satisfying `P`. -/
def IsNegOf (P : ((V → ℤ) → WithTop ℝ) → Prop) (F : (V → ℤ) → EReal) : Prop :=
  ∃ h : (V → ℤ) → WithTop ℝ, P h ∧ ∀ x, F x = -ToEReal (h x)

end DiscreteConvex.ConjugacyDualityD


