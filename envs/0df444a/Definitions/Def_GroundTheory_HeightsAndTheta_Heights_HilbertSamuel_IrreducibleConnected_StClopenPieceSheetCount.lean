-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StClopenPieceSheetCount
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StClopenPieceSheetCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:34.001976+00:00
-- url     : https://prove2.me/theorems/669b9c79-815c-4ba5-8a04-edc38829cf5c
-- title:
--   St Clopen Piece Sheet Count
-- statement:
--   Definitions and structural lemmas for St Clopen Piece Sheet Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/StClopenPieceSheetCount.lean

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
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open Matrix
def ClopenPieceSheetCount.Statement : Prop :=
  ∀ (n d N : ℕ) (A : Matrix (Fin d) (Fin n) ℂ) (Z : Set (Fin n → ℂ)) (Ω : Set (Fin d → ℂ))
    (O F : Set (Fin n → ℂ)),
    IsOpen Ω → IsPreconnected Ω →
    (∀ y ∈ Ω, {x | x ∈ Z ∧ A *ᵥ x = y}.Finite ∧ {x | x ∈ Z ∧ A *ᵥ x = y}.ncard = N ∧
      ∀ x ∈ Z, A *ᵥ x = y → ∃ (U : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
        (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen U ∧ y ∈ U ∧ IsOpen V ∧ x ∈ V ∧
          ContinuousOn g U ∧ g y = x ∧ (∀ w ∈ U, A *ᵥ g w = w) ∧ Z ∩ V = g '' U) →
    IsOpen O → IsClosed F →
    {x | x ∈ Z ∧ A *ᵥ x ∈ Ω} ∩ O = {x | x ∈ Z ∧ A *ᵥ x ∈ Ω} ∩ F →
    ∃ k : ℕ, ∀ y ∈ Ω, {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y}.ncard = k
end GroundTheory.Heights₂.Heights.HilbertSamuel


