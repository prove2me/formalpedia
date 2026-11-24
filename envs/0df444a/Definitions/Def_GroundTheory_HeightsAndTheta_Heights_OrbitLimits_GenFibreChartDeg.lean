-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GenFibreChartDeg
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GenFibreChartDeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:06.909659+00:00
-- url     : https://prove2.me/theorems/49dc9219-9435-41b8-8b78-6412747f7d6c
-- title:
--   Gen Fibre Chart Deg
-- statement:
--   Definitions and structural lemmas for Gen Fibre Chart Deg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GenFibreChartDeg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_FibreCurve
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
def GenFibreChartDeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (G : GenFibre v P')
    [CharZero G.Φ'] (c : ∀ k, ι k) (i : ∀ k : FibreBlock κ, fibreIdx ι' κ k),
    IsBlockMap κ v → IsMultiHomogIdeal P' → (∀ k, G.x ⟨k, c k⟩ ≠ 0) → (∀ k, G.x' ⟨k.1, i k⟩ ≠ 0) →
    Module.finrank G.Φ (IntermediateField.adjoin G.Φ (Set.range fun q : Σ k : FibreBlock κ, fibreIdx ι' κ k =>
        G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩)) =
      IntermediateField.relfinrank (blockFnField (G.x' ∘ v)) (blockFnField G.x')
end GroundTheory.Heights₂.Heights.Targets


