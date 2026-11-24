-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormMinimalFactorPoints
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormMinimalFactorPoints
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:25.527798+00:00
-- url     : https://prove2.me/theorems/4999ece1-bc96-4613-9bea-00499cad98e9
-- title:
--   St Primitive Form Minimal Factor Points
-- statement:
--   Definitions and structural lemmas for St Primitive Form Minimal Factor Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPrimitiveFormMinimalFactorPoints.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedOffDiscriminant
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
def PrimitiveFormMinimalFactorPoints.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∀ (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
      (q : σ → Fin N → (Fin d → ℂ) → ℂ),
      (∀ j, AnalyticAt ℂ (a j) (A w)) → AnalyticAt ℂ δ (A w) → (∀ i j, AnalyticAt ℂ (q i j) (A w)) →
      (¬ ∀ᶠ y in 𝓝 (A w), δ y = 0) →
      (∀ᶠ z in 𝓝 w, z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) →
      (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
        (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) →
      (∀ i, ∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
      ∃ (n : ℕ) (b : Fin n → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (b j) (A w)) ∧
        (∀ᶠ z in 𝓝 w, z ∈ X → ℓ z ^ n + ∑ j, b j (A z) * ℓ z ^ (j : ℕ) = 0) ∧
        (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
          (Polynomial.X ^ n + ∑ j, Polynomial.C (b j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) ∧
        ∀ U ∈ 𝓝 w, ∀ᶠ y in 𝓝 (A w), δ y ≠ 0 → ∀ τ : ℂ, τ ^ n + ∑ j, b j y * τ ^ (j : ℕ) = 0 →
          (fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y) ∈ X ∩ U ∧
            A (fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y) = y ∧
            ℓ (fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y) = τ
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


