-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AlgebraMapMemO
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_AlgebraMapMemO
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T05:24:45.991088+00:00
-- url     : https://prove2.me/theorems/228729c4-3a06-578b-b843-bffa912dbd7d
-- title:
--   Algebra Map Mem O
-- statement:
--   Definitions and structural lemmas for Algebra Map Mem O, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AlgebraMapMemO.lean

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel
namespace GlobalTheory.CommonDenominator
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
end GlobalTheory.CommonDenominator


