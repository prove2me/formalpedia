-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedIffRootFull
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedIffRootFull
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:47.069035+00:00
-- url     : https://prove2.me/theorems/a5ad81ef-3d40-4229-93e1-db66cae11282
-- title:
--   St Primitive Form Sheeted Iff Root Full
-- statement:
--   Definitions and structural lemmas for St Primitive Form Sheeted Iff Root Full, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPrimitiveFormSheetedIffRootFull.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedLocusCutOut
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
open Topology
def PrimitiveFormRootFull {σ : Type} [Fintype σ] {d N : ℕ} (X W : Set (σ → ℂ))
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ) (δ : (Fin d → ℂ) → ℂ)
    (q : σ → Fin N → (Fin d → ℂ) → ℂ) (t : Fin d → ℂ) (τ : ℂ) : Prop :=
  ∃ (O : Set (Fin d → ℂ)) (r : (Fin d → ℂ) → ℂ), IsOpen O ∧ t ∈ O ∧ AnalyticOnNhd ℂ r O ∧ r t = τ ∧
    ∀ s ∈ O, (fun i : σ => (∑ j, q i j s * r s ^ (j : ℕ)) / δ s) ∈ X ∩ W ∧
      A (fun i : σ => (∑ j, q i j s * r s ^ (j : ℕ)) / δ s) = s ∧
      ℓ (fun i : σ => (∑ j, q i j s * r s ^ (j : ℕ)) / δ s) = r s
def PrimitiveFormSheetedIffRootFull.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
    (q : σ → Fin N → (Fin d → ℂ) → ℂ),
    (∀ j, AnalyticAt ℂ (a j) (A w)) → AnalyticAt ℂ δ (A w) → (∀ i j, AnalyticAt ℂ (q i j) (A w)) →
    (∀ᶠ z in 𝓝 w, z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) →
    (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
      (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) →
    (∀ i, ∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
    ∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) ≠ 0 → ∀ W : Set (σ → ℂ), IsOpen W → z ∈ W →
      ((∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧
            z ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ t ∈ O, A (g t) = t) ∧ X ∩ V = g '' O) ↔
        PrimitiveFormRootFull X W A ℓ δ q (A z) (ℓ z))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


