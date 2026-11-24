-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GenericCountCover
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GenericCountCover
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:37.207464+00:00
-- url     : https://prove2.me/theorems/acd0b5c5-ddac-4641-a22e-9232bd62a7a1
-- title:
--   Generic Count Cover
-- statement:
--   Definitions and structural lemmas for Generic Count Cover, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GenericCountCover.lean

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
open Topology
def IsGenericCountCover {σ : Type} [Fintype σ] {d : ℕ} (Y : Set (σ → ℂ)) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (D : Set (Fin d → ℂ)) (N : ℕ) : Prop :=
  (∀ y ∈ D, {x | x ∈ Y ∧ A x = y}.encard ≤ N) ∧
  ∀ y₀ ∈ D, ∃ (U : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → ℂ),
    IsOpen U ∧ y₀ ∈ U ∧ U ⊆ D ∧ AnalyticOnNhd ℂ g U ∧
    (∀ W : Set (Fin d → ℂ), IsOpen W → W ⊆ U → W.Nonempty → ∃ t ∈ W, g t ≠ 0) ∧
    ∀ y ∈ U, g y ≠ 0 → {x | x ∈ Y ∧ A x = y}.encard = N ∧
      ∀ x ∈ Y, A x = y → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
        IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ h O ∧ (∀ y' ∈ O, A (h y') = y') ∧ Y ∩ V = h '' O
noncomputable def fibreDiscr {σ : Type} [Fintype σ] {d : ℕ} (Y : Set (σ → ℂ)) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (l : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (y : Fin d → ℂ) : ℂ :=
  if h : {x | x ∈ Y ∧ A x = y}.encard = N then
    ∏ p ∈ (Set.finite_of_encard_eq_coe h).toFinset.offDiag, (l p.1 - l p.2)
  else 0
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


