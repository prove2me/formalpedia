-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralLeOfSection
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralLeOfSection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:54:25.659805+00:00
-- url     : https://prove2.me/theorems/94af89c2-9000-4f7a-b35d-2c35b8c6a3e9
-- title:
--   Lintegral Le Of Section
-- statement:
--   Definitions and structural lemmas for Lintegral Le Of Section, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LintegralLeOfSection.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
namespace GlobalTheory.FrameSplit
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end GlobalTheory.FrameSplit


