-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeChartBoundsOfSchurLemW
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeChartBoundsOfSchurLemW
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T23:57:24.861817+00:00
-- url     : https://prove2.me/theorems/804adb9b-0d4b-409a-bb51-a451cdfef25d
-- title:
--   Hodge Chart Bounds Of Schur Lem W
-- statement:
--   Definitions and structural lemmas for Hodge Chart Bounds Of Schur Lem W, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeChartBoundsOfSchurLemW.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PeriodChartUniformConstantsHalfPolydiscStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeMetricGramMatrixLocalHolomorphicImPartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PoincareMetricPuncturedPolydiscBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConnectionMatrixGramOperatorNormLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeCurvatureDualMetricPointwiseBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChernCurvatureFormSelfEqDualNormStatement
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
namespace GlobalTheory.HodgeChartRow
end GlobalTheory.HodgeChartRow


