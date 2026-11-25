-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_PointwiseNormConstantSection
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_PointwiseNormConstantSection
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T16:19:58.802001+00:00
-- url     : https://prove2.me/theorems/c99506fd-71e8-46d3-a7bc-822bdc487090
-- title:
--   Pointwise Norm Constant Section
-- statement:
--   Definitions and structural lemmas for Pointwise Norm Constant Section, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/PointwiseNormConstantSection.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IndependentSectionsUpperCount
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_TaylorExpansionLocalCoordinates
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_LintegralBallRpowLtTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR
open MeasureTheory Filter Topology Asymptotics ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal
noncomputable section
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La)
end
end ReciprocityTheory.ChartRestriction.G.AR


