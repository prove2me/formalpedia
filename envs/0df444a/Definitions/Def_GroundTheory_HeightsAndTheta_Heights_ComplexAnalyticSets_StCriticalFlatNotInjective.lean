-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCriticalFlatNotInjective
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCriticalFlatNotInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:45.659805+00:00
-- url     : https://prove2.me/theorems/ca20f0db-22d3-46b2-8cdc-6633f13580c2
-- title:
--   St Critical Flat Not Injective
-- statement:
--   Definitions and structural lemmas for St Critical Flat Not Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCriticalFlatNotInjective.lean

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
def CriticalFlatNotInjective.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin k → ℂ) (a : Fin k → ℂ),
    2 ≤ k → IsOpen U → DifferentiableOn ℂ f U → a ∈ U →
    LinearMap.det (fderiv ℂ f a : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) = 0 →
    (∀ b ∈ U, LinearMap.det (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) = 0 → fderiv ℂ f b = 0) →
    ¬ Set.InjOn f U
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


