-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ProperIdealsOfHenselian
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_ProperIdealsOfHenselian
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T05:25:16.495293+00:00
-- url     : https://prove2.me/theorems/43ac207c-d312-43e6-8c60-8682022d1cb1
-- title:
--   Proper Ideals Of Henselian
-- statement:
--   Definitions and structural lemmas for Proper Ideals Of Henselian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ProperIdealsOfHenselian.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.UnramOrder
section Abstract
open IsLocalRing Polynomial
variable {R₀ R : Type*} [CommRing R₀] [CommRing R] [Algebra R₀ R]
end Abstract
end GlobalTheory.UnramOrder


