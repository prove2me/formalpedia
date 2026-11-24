-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartScalingIndep
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PChartScalingIndep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:42.643351+00:00
-- url     : https://prove2.me/theorems/33e13df0-51e4-476c-bd24-60ac16da27de
-- title:
--   PChart Scaling Indep
-- statement:
--   Definitions and structural lemmas for PChart Scaling Indep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartScalingIndep.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartScalingIndep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
namespace ChartScalingIndep
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {K : Type} [Fintype K] [DecidableEq K]
  {ι : K → Type} [∀ k, Fintype (ι k)]
end ChartScalingIndep
end GroundTheory.Heights₂.Heights.Inter


