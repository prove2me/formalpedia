-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBisFurther
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBisFurther
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T05:13:33.31806+00:00
-- url     : https://prove2.me/theorems/a7d48eaa-1014-5702-939f-2f24ed3c8031
-- title:
--   Imports Bis Further
-- statement:
--   Definitions and structural lemmas for Imports Bis Further, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ImportsBisFurther.lean

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
namespace GlobalTheory.PowMulMemOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
end GlobalTheory.PowMulMemOrder


