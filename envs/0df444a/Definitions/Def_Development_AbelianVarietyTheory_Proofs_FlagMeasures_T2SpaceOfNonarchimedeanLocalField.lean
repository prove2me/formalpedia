-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfNonarchimedeanLocalField
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfNonarchimedeanLocalField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:51.6524+00:00
-- url     : https://prove2.me/theorems/24b19290-d31e-4c1c-8da8-f93ccd23d01a
-- title:
--   T2 Space Of Nonarchimedean Local Field
-- statement:
--   Definitions and structural lemmas for T2 Space Of Nonarchimedean Local Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceOfNonarchimedeanLocalField.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIntegersLocalisationIffSumCmDataStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors
namespace GlobalTheory.LocAtTopology
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
end GlobalTheory.LocAtTopology


