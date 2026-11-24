-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCentredDiscCoverCurve
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCentredDiscCoverCurve
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:58.515839+00:00
-- url     : https://prove2.me/theorems/e9cce812-4a0a-45c7-b503-9933807f8f0e
-- title:
--   St Centred Disc Cover Curve
-- statement:
--   Definitions and structural lemmas for St Centred Disc Cover Curve, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCentredDiscCoverCurve.lean

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
open Topology Filter Metric
def IsCentredDiscCover {σ : Type} [Fintype σ] (Y : Set (σ → ℂ)) (w : σ → ℂ) (p : (σ → ℂ) →L[ℂ] ℂ)
    (ρ : ℝ) (N : ℕ) : Prop :=
  w ∈ Y ∧ 0 < N ∧ Set.MapsTo p Y (ball (p w) ρ) ∧ (∀ x ∈ Y, p x = p w → x = w) ∧
    (∀ t ∈ ball (p w) ρ, t ≠ p w → {x | x ∈ Y ∧ p x = t}.encard = N) ∧
    (∀ K ⊆ ball (p w) ρ, IsCompact K → IsCompact {x | x ∈ Y ∧ p x ∈ K}) ∧
    (∀ x ∈ Y, p x ≠ p w → ∃ (O : Set ℂ) (V : Set (σ → ℂ)) (g : ℂ → σ → ℂ), IsOpen O ∧ IsOpen V ∧ x ∈ V ∧
      DifferentiableOn ℂ g O ∧ (∀ t ∈ O, p (g t) = t) ∧ Y ∩ V = g '' O)
def CentredDiscCoverCurve.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (w : σ → ℂ) (p : (σ → ℂ) →L[ℂ] ℂ) (ρ : ℝ) (N : ℕ),
    IsCentredDiscCover Y w p ρ N →
      ∃ r : ℝ, 0 < r ∧ ∃ γ : ℂ → σ → ℂ,
        DifferentiableOn ℂ γ (ball 0 r) ∧ Set.InjOn γ (ball 0 r) ∧ γ 0 = w ∧ Set.MapsTo γ (ball 0 r) Y
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


