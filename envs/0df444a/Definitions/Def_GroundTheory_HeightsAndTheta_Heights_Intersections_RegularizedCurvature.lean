-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegularizedCurvature
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_RegularizedCurvature
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:39.12432+00:00
-- url     : https://prove2.me/theorems/685bb666-fc8f-4473-8e4a-d783133e7b5a
-- title:
--   Regularized Curvature
-- statement:
--   Definitions and structural lemmas for Regularized Curvature, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegularizedCurvature.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
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
namespace RegularizedCurvature
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian
set_option linter.unusedSectionVars false
section Second
variable {J : Type} [Fintype J]
end Second
section Holo
variable {J : Type} [Fintype J]
end Holo
section LogSum
variable {J : Type} [Fintype J]
end LogSum
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
end RegularizedCurvature
end GroundTheory.Heights₂.Heights.Inter


