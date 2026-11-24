-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeCurvatureDualMetricPointwiseBound
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeCurvatureDualMetricPointwiseBound
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T23:44:38.761794+00:00
-- url     : https://prove2.me/theorems/c53c89cf-79f2-4c63-bc72-a44c8d8e55e0
-- title:
--   Hodge Curvature Dual Metric Pointwise Bound
-- statement:
--   Definitions and structural lemmas for Hodge Curvature Dual Metric Pointwise Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeCurvatureDualMetricPointwiseBound.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
namespace GlobalTheory.HodgeCurvPoint
variable {g : ℕ}
end GlobalTheory.HodgeCurvPoint


