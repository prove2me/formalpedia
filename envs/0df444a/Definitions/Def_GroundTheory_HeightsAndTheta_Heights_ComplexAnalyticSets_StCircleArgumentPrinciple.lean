-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCircleArgumentPrinciple
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCircleArgumentPrinciple
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:15.822949+00:00
-- url     : https://prove2.me/theorems/87419463-00de-4ee9-9e7e-000d09bf950e
-- title:
--   St Circle Argument Principle
-- statement:
--   Definitions and structural lemmas for St Circle Argument Principle, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCircleArgumentPrinciple.lean

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
open Topology Filter Metric Complex Real
noncomputable section
def CircleArgumentPrinciple.Statement : Prop :=
  ∀ (h : ℂ → ℂ) (O : Set ℂ) (c : ℂ) (r : ℝ),
    0 < r → IsOpen O → closedBall c r ⊆ O → DifferentiableOn ℂ h O → (∀ s ∈ sphere c r, h s ≠ 0) →
    ∃ (Z : Multiset ℂ) (u : ℂ → ℂ),
      (∀ a ∈ Z, a ∈ ball c r) ∧ DifferentiableOn ℂ u O ∧ (∀ s ∈ closedBall c r, u s ≠ 0) ∧
      (∀ s ∈ O, h s = (Z.map fun a => s - a).prod * u s) ∧
      ∀ φ : ℂ → ℂ, DifferentiableOn ℂ φ O →
        (2 * π * I)⁻¹ * (∮ s in C(c, r), φ s * deriv h s / h s) = (Z.map φ).sum
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


