-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayCountThetaFibreCount
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayCountThetaFibreCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:10:22.334833+00:00
-- url     : https://prove2.me/theorems/fcb3c9e9-4462-4051-b401-300bb90518e5
-- title:
--   Ray Count Theta Fibre Count
-- statement:
--   Definitions and structural lemmas for Ray Count Theta Fibre Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayCountThetaFibreCount.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QFormCountStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ThetaQFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassIdealCountEqNcardShiftedBinaryFormStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
namespace GlobalTheory.Hk
end GlobalTheory.Hk


