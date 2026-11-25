-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AdditionLevelTwoMul
-- name    : Development_AbelianVarietyTheory_Proofs_ToricGeometry_AdditionLevelTwoMul
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T16:38:36.671153+00:00
-- url     : https://prove2.me/theorems/58827ce3-a16d-4df0-b003-c371a4d23617
-- title:
--   Addition Level Two Mul
-- statement:
--   Definitions and structural lemmas for Addition Level Two Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AdditionLevelTwoMul.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SpanEvalEqTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
namespace GlobalTheory.ThetaAddition
end GlobalTheory.ThetaAddition


