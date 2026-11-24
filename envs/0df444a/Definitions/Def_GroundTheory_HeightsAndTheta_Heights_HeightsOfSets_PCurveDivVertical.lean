-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveDivVertical
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveDivVertical
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:26.200166+00:00
-- url     : https://prove2.me/theorems/335e84d7-299a-49d1-9b0d-3290ce8e0276
-- title:
--   PCurve Div Vertical
-- statement:
--   Definitions and structural lemmas for PCurve Div Vertical, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/PCurveDivVertical.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace CurveDivVertical
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open Classical
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
open Classical in

def wt (T : Finset K) : (Σ k, ι k) → ℕ := fun p ↦ if p.1 ∈ T then 1 else 0
def proj (T : Finset K) : MRing ι →+* MRing ι :=
  GradedRing.projZeroRingHom (weightedHomogeneousSubmodule ℤ (wt (ι := ι) T))
end CurveDivVertical
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet


