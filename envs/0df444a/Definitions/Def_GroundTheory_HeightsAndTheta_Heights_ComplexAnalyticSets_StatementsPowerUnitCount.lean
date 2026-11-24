-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsPowerUnitCount
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsPowerUnitCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:27.232967+00:00
-- url     : https://prove2.me/theorems/4009b626-3213-4863-8328-ab9040a0c621
-- title:
--   Statements Power Unit Count
-- statement:
--   Definitions and structural lemmas for Statements Power Unit Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsPowerUnitCount.lean

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
open Filter Topology Matrix
noncomputable section
def PowerUnitCount.Statement : Prop :=
  ∀ (d m : ℕ) (O : Set (Fin (d + 1) → ℂ)) (F : (Fin (d + 1) → ℂ) → Fin d → ℂ)
    (H : (Fin (d + 1) → ℂ) → ℂ) (s : Fin (d + 1) → ℂ),
    IsOpen O → s ∈ O → s 0 = 0 → DifferentiableOn ℂ F O → DifferentiableOn ℂ H O → H s ≠ 0 →
    Function.Bijective (fderiv ℂ (fun τ => vecCons (τ 0) (F τ)) s) →
    ∃ P₀ ∈ 𝓝 s, Set.InjOn F (P₀ ∩ {τ | τ 0 = 0}) ∧
      ∀ P ∈ 𝓝 s, P ⊆ P₀ → ∃ (V : Set (Fin d → ℂ)) (ρ : ℝ), IsOpen V ∧ F s ∈ V ∧ 0 < ρ ∧
        (∀ w ∈ V, ∀ τ ∈ P₀, τ 0 = 0 → F τ = w → τ ∈ P) ∧
        ∀ w ∈ V, ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ →
          {τ | τ ∈ P ∧ F τ = w ∧ τ 0 ^ m * H τ = t}.encard = m
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


