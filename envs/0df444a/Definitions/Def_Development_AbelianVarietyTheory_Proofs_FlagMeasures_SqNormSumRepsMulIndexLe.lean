-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SqNormSumRepsMulIndexLe
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_SqNormSumRepsMulIndexLe
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T05:25:23.062163+00:00
-- url     : https://prove2.me/theorems/6ac4d3e7-a83d-4ac8-ab3f-7d83c9c0cd20
-- title:
--   Sq Norm Sum Reps Mul Index Le
-- statement:
--   Definitions and structural lemmas for Sq Norm Sum Reps Mul Index Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SqNormSumRepsMulIndexLe.lean

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
open scoped Pointwise ENNReal Classical ComplexConjugate
namespace GlobalTheory.HL.GaussSum
end GlobalTheory.HL.GaussSum


