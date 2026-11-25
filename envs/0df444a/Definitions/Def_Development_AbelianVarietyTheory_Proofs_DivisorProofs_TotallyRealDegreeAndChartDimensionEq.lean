-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TotallyRealDegreeAndChartDimensionEq
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_TotallyRealDegreeAndChartDimensionEq
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:30:23.190322+00:00
-- url     : https://prove2.me/theorems/b38e9316-69c7-4a43-9e87-c0e3b86f01b5
-- title:
--   Totally Real Degree And Chart Dimension Eq
-- statement:
--   Definitions and structural lemmas for Totally Real Degree And Chart Dimension Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TotallyRealDegreeAndChartDimensionEq.lean

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__TamagawaSpecialUnitary_320f37a25cd91d38
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PhaseFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal
namespace GlobalTheory.ChartCount
end GlobalTheory.ChartCount


