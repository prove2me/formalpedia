-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormWindow
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormWindow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:53.881078+00:00
-- url     : https://prove2.me/theorems/4d968b85-d16f-4a5b-8dba-04dd8f501f1c
-- title:
--   St Primitive Form Window
-- statement:
--   Definitions and structural lemmas for St Primitive Form Window, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPrimitiveFormWindow.lean

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
def PrimitiveFormWindow.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    ∀ (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
      (q : σ → Fin N → (Fin d → ℂ) → ℂ),
      (∀ j, AnalyticAt ℂ (a j) (A w)) → AnalyticAt ℂ δ (A w) → (∀ i j, AnalyticAt ℂ (q i j) (A w)) →
      (∀ᶠ z in 𝓝 w, z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) →
      (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
        (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) →
      (∀ i, ∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
      ∃ (W : Set (σ → ℂ)) (B : Set (Fin d → ℂ)) (N' : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ),
        IsOpen W ∧ w ∈ W ∧ IsOpen B ∧ Convex ℝ B ∧ A w ∈ B ∧
        IsOpen N' ∧ closure W ⊆ N' ∧ (∀ i, AnalyticOnNhd ℂ (f i) N') ∧
        X ∩ N' = {z | z ∈ N' ∧ ∀ i, f i z = 0} ∧
        (∀ z ∈ X ∩ closure W, A z ∈ B → z ∈ W) ∧
        (∀ z ∈ X ∩ W, ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) ∧
        (∀ i, ∀ z ∈ X ∩ W, δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) ∧
        (∀ j, AnalyticOnNhd ℂ (a j) B) ∧ AnalyticOnNhd ℂ δ B ∧ (∀ i j, AnalyticOnNhd ℂ (q i j) B) ∧
        (∀ y ∈ B, δ y ≠ 0 →
          (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


