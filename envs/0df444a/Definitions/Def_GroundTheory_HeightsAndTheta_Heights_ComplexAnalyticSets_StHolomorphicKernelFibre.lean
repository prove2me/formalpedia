-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicKernelFibre
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicKernelFibre
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:58.302586+00:00
-- url     : https://prove2.me/theorems/c6159575-b654-4396-8b13-dd47364a744c
-- title:
--   St Holomorphic Kernel Fibre
-- statement:
--   Definitions and structural lemmas for St Holomorphic Kernel Fibre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StHolomorphicKernelFibre.lean

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
def HolomorphicKernelFibre.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin k → ℂ) (b : Fin k → ℂ),
    IsOpen U → DifferentiableOn ℂ f U → b ∈ U →
    ∀ d : ℕ, Module.finrank ℂ (LinearMap.ker (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)) = d →
      ∃ (V : Set (Fin d → ℂ)) (y : Fin d → ℂ) (γ : (Fin d → ℂ) → Fin k → ℂ)
        (ℓ : (Fin k → ℂ) →L[ℂ] Fin d → ℂ),
        IsOpen V ∧ y ∈ V ∧ DifferentiableOn ℂ γ V ∧ Set.MapsTo γ V U ∧ Set.InjOn γ V ∧
          (∀ s ∈ V, ∀ t ∈ V, ℓ (f (γ s)) = ℓ (f (γ t)) → f (γ s) = f (γ t)) ∧
          fderiv ℂ (fun t => ℓ (f (γ t))) y = 0
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


