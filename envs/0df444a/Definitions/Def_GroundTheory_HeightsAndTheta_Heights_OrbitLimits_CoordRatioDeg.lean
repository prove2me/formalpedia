-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CoordRatioDeg
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CoordRatioDeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:20.116721+00:00
-- url     : https://prove2.me/theorems/84f163ff-8cff-476d-a4e1-ba0795e704e0
-- title:
--   Coord Ratio Deg
-- statement:
--   Definitions and structural lemmas for Coord Ratio Deg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/CoordRatioDeg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
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
def CoordRatioDeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k', ι' k') → Ω) (Φ' : Type) [Field Φ'] [CharZero Φ'] (x' : (Σ k', ι' k') → Φ'),
    IsBlockMap κ v → RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Φ') = mCoordIdeal y →
    IntermediateField.relfinrank (blockFnField (x' ∘ v)) (blockFnField x') =
      IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y)
end GroundTheory.Heights₂.Heights.Targets


