-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ParametricIntegralSmoothness_IntCommute
-- name    : CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ParametricIntegralSmoothness_IntCommute
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T04:30:53.098538+00:00
-- url     : https://prove2.me/theorems/67a117c2-1892-4947-b7de-808ccd9d0583
-- title:
--   Int Commute
-- statement:
--   Definitions and structural lemmas for Int Commute, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ParametricIntegralSmoothness/IntCommute.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SigmaFiniteQuotients_Exists
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff Manifold Convolution
noncomputable section
namespace CompanionTheory.D.Upq.Sm
open PI CompanionTheory.D.Upq.ModEx
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)} {hG : IsMatGroup G}
section Group
variable {μ : Measure (MG G hG)} [IsFiniteMeasureOnCompacts μ] {φ : MG G hG → ℂ}
end Group
end CompanionTheory.D.Upq.Sm
end


