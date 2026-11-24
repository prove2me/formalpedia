-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PTorusInvLevi
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PTorusInvLevi
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:23.152442+00:00
-- url     : https://prove2.me/theorems/344f9e3a-7100-4051-be21-086e9116f820
-- title:
--   PTorus Inv Levi
-- statement:
--   Definitions and structural lemmas for PTorus Inv Levi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PTorusInvLevi.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StTorusInvLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
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
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
namespace TorusInvariantLevi
set_option linter.unusedSectionVars false
section Vectors
variable {J : Type} [Fintype J]
end Vectors
section Blocks
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def blk (k : K) : ((Σ k, ι k) → ℂ) →L[ℂ] (ι k → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι k) => ℂ) ⟨k, i⟩
end Blocks
end TorusInvariantLevi
end GroundTheory.Heights₂.Heights.Inter


