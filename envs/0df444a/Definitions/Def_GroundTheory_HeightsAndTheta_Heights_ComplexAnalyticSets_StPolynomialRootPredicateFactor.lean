-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolynomialRootPredicateFactor
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolynomialRootPredicateFactor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:41.644004+00:00
-- url     : https://prove2.me/theorems/1c4d94cd-1ff7-48de-aa06-b5ed89629530
-- title:
--   St Polynomial Root Predicate Factor
-- statement:
--   Definitions and structural lemmas for St Polynomial Root Predicate Factor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPolynomialRootPredicateFactor.lean

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
def PolynomialRootPredicateFactor.Statement : Prop :=
  ∀ (d N : ℕ) (B : Set (Fin d → ℂ)) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
    (P : (Fin d → ℂ) → ℂ → Prop),
    IsOpen B → Convex ℝ B → (∀ j, AnalyticOnNhd ℂ (a j) B) → AnalyticOnNhd ℂ δ B → (∃ t ∈ B, δ t ≠ 0) →
    (∀ t ∈ B, δ t ≠ 0 →
      (Polynomial.X ^ N + ∑ j, Polynomial.C (a j t) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) →
    (∀ t₀ ∈ B, δ t₀ ≠ 0 → ∀ τ₀ : ℂ, τ₀ ^ N + ∑ j, a j t₀ * τ₀ ^ (j : ℕ) = 0 →
      ∃ (O : Set (Fin d → ℂ)) (r : (Fin d → ℂ) → ℂ), IsOpen O ∧ t₀ ∈ O ∧ ContinuousOn r O ∧ r t₀ = τ₀ ∧
        ∀ s ∈ O, r s ^ N + ∑ j, a j s * r s ^ (j : ℕ) = 0 ∧ (P s (r s) ↔ P t₀ τ₀)) →
    ∃ C E : (Fin d → ℂ) → ℂ → ℂ,
      (∀ t ∈ B, ∀ T : ℂ, AnalyticAt ℂ (fun u : (Fin d → ℂ) × ℂ => C u.1 u.2) (t, T) ∧
        AnalyticAt ℂ (fun u : (Fin d → ℂ) × ℂ => E u.1 u.2) (t, T)) ∧
      (∀ t ∈ B, ∀ T : ℂ, C t T * E t T = T ^ N + ∑ j, a j t * T ^ (j : ℕ)) ∧
      ∀ t ∈ B, δ t ≠ 0 → ∀ τ : ℂ, τ ^ N + ∑ j, a j t * τ ^ (j : ℕ) = 0 →
        (C t τ = 0 ↔ P t τ) ∧ (E t τ = 0 ↔ ¬ P t τ)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


