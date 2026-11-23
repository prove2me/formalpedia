-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeSectionFacesAndDoubling
-- name    : Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeSectionFacesAndDoubling
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:38.264192+00:00
-- url     : https://prove2.me/theorems/c4bfcb8b-4828-4e7f-9f1d-46eda3397ed0
-- title:
--   Cube Section Faces And Doubling
-- statement:
--   Definitions and structural lemmas for Cube Section Faces And Doubling, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeSectionFacesAndDoubling.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
namespace GlobalTheory
namespace CubeFace
def diagChart {ι : Type*} (a b d o : ι) (J : Finset (Fin 3)) : ι :=
  if J = {2} then b else if J = {0, 1} then d
  else if J = {0} ∨ J = {1} ∨ J = {0, 1, 2} then a else o
section Main
variable {g : ℕ} {ι : Type} (W : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ)
  (hW : ∀ i, IsOpen (W i)) (hcov : ∀ z, ∃ i, z ∈ W i)
  (hc0 : ∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0)
  (hcc : ∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z)
  (T : (Finset (Fin 3) → ι) → (Fin 3 → Fin g → ℂ) → ℂ)
  (hT : ∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))})
  (hT0 : ∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0)
  (hTT : ∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
    (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) →
    T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) *
      T j' x)
  (Λ : Submodule ℤ (Fin g → ℂ)) (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
  (hWp : ∀ i z, ∀ l ∈ Λ, z + l ∈ W i ↔ z ∈ W i)
  (hTp : ∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) → T j (x + l) = T j x)
  (i₀ : ι) (h0 : (0 : Fin g → ℂ) ∈ W i₀)
end Main
end CubeFace
end GlobalTheory


