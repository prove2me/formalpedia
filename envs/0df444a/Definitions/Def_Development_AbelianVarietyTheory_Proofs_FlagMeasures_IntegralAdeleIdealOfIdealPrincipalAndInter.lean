-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegralAdeleIdealOfIdealPrincipalAndInter
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegralAdeleIdealOfIdealPrincipalAndInter
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T12:39:31.428428+00:00
-- url     : https://prove2.me/theorems/61c5e495-737e-49ef-aa05-00bee2a70be1
-- title:
--   Integral Adele Ideal Of Ideal Principal And Inter
-- statement:
--   Definitions and structural lemmas for Integral Adele Ideal Of Ideal Principal And Inter, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IntegralAdeleIdealOfIdealPrincipalAndInter.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
namespace GlobalTheory.RowLev
open Formalism.UG Formalism.UG.P Inhab
section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
noncomputable def intAdIncl (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    intAd F →+* IntAf F E :=
  ((Algebra.TensorProduct.includeRight : Af F →ₐ[F] E ⊗[F] Af F).toRingHom.comp (intAd F).subtype).codRestrict _
    fun y => Subring.subset_closure (Or.inr ⟨y, rfl⟩)
end
end GlobalTheory.RowLev


