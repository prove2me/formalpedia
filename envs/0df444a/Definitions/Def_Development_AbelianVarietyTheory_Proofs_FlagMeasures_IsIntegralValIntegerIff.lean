-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralValIntegerIff
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralValIntegerIff
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T05:20:10.776334+00:00
-- url     : https://prove2.me/theorems/c0897457-218b-4985-b7ac-47e0bcab8ae5
-- title:
--   Is Integral Val Integer Iff
-- statement:
--   Definitions and structural lemmas for Is Integral Val Integer Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsIntegralValIntegerIff.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc GlobalTheory.SgLoc
open scoped ComplexOrder
namespace GlobalTheory.SgLoc
noncomputable def idemPairHom {F E : Type} [Field F] [CommRing E] [Algebra F E] (p q : E)
    (h1 : p + q = 1) (h0 : p * q = 0) : F × F →ₐ[F] E :=
  AlgHom.ofLinearMap
    ((LinearMap.toSpanSingleton F E p).coprod (LinearMap.toSpanSingleton F E q))
    (by simpa using h1)
    (by
      rintro ⟨a, b⟩ ⟨c, d⟩
      simp only [Prod.mk_mul_mk, LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply,
        Algebra.smul_def, map_mul]
      linear_combination
        (-(algebraMap F E a * algebraMap F E c * p) - algebraMap F E b * algebraMap F E d * q) * h1
        + (algebraMap F E a * algebraMap F E c + algebraMap F E b * algebraMap F E d
          - algebraMap F E a * algebraMap F E d - algebraMap F E b * algebraMap F E c) * h0)
end GlobalTheory.SgLoc


