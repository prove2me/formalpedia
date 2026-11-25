-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_KFinFormOf
-- name    : CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_KFinFormOf
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T03:07:14.996497+00:00
-- url     : https://prove2.me/theorems/71560400-1ca9-41ce-9d0d-63069b41ff21
-- title:
--   KFin Form Of
-- statement:
--   Definitions and structural lemmas for KFin Form Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/BesselOrbitConvolutions/KFinFormOf.lean

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L2NormScaling
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
namespace CompanionTheory.D.Upq.BesselFunctionalConstruction
open Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DDSmoothness
def RankOne : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx k r → (H →L[ℂ] H)) (w0 : H) (Wp : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 z Formalism.QuantumDeterminants.cStd u π μW μN μG νq →
    ∃ L : H → Wp, ∀ w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
        be z Formalism.QuantumDeterminants.cStd π σ μW μN w v = (innerSL ℂ (L v)).smulRight (L w)
end CompanionTheory.D.Upq.BesselFunctionalConstruction
end


