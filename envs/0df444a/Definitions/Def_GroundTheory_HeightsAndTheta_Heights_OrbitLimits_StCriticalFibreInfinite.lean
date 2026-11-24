-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StCriticalFibreInfinite
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StCriticalFibreInfinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:20.704517+00:00
-- url     : https://prove2.me/theorems/ddcc52a9-93b3-46b2-b8b6-c5e3d9c3b26a
-- title:
--   St Critical Fibre Infinite
-- statement:
--   Definitions and structural lemmas for St Critical Fibre Infinite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StCriticalFibreInfinite.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
noncomputable section
def CriticalFibreInfinite.Statement : Prop :=
  ∀ (k d : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin d → ℂ),
    IsOpen U → U.Nonempty → DifferentiableOn ℂ f U →
      (∀ t ∈ U, ¬ Function.Injective (fderiv ℂ f t)) →
        ∃ y : Fin d → ℂ, {t | t ∈ U ∧ f t = y}.Infinite
end
end GroundTheory.Heights₂.Heights


