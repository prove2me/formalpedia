-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemiPosTwist
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PSemiPosTwist
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:54.922806+00:00
-- url     : https://prove2.me/theorems/b35d7598-0b29-4dc4-be4e-efc4ceab0b6e
-- title:
--   PSemi Pos Twist
-- statement:
--   Definitions and structural lemmas for PSemi Pos Twist, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemiPosTwist.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StTorusInvLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
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
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian
namespace SemipositiveTwist
set_option linter.unusedSectionVars false
section Blocks
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def blk (k : K) : ((Σ k, ι k) → ℂ) →L[ℂ] (ι k → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι k) => ℂ) ⟨k, i⟩
def F (k : K) (y : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log ((fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩))
end Blocks
section Levi
variable {J : Type} [Fintype J]
end Levi
end SemipositiveTwist
end GroundTheory.Heights₂.Heights.Inter


