-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PChartSectionNotMem
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PChartSectionNotMem
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T16:16:40.54292+00:00
-- url     : https://prove2.me/theorems/9207653f-c0e6-4c7c-b615-dddc65c7d576
-- title:
--   PChart Section Not Mem
-- statement:
--   Definitions and structural lemmas for PChart Section Not Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PChartSectionNotMem.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothMetricOfIsSmoothHerm
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
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
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial Algebra
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsSectionOn mcPts segre)
namespace ChartSectionNotMem
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def coneMap (𝔮 : Ideal (MvPolynomial (Σ k, ι k) ℂ)) :
    MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) :=
  aeval fun q => X q.1 * C (Ideal.Quotient.mk 𝔮 (X q))
end ChartSectionNotMem
end GroundTheory.Heights₂.Heights.Targets


