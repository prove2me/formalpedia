-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPieceRootProductPolynomial
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPieceRootProductPolynomial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:33.361522+00:00
-- url     : https://prove2.me/theorems/3fdc263f-cf0c-4b42-be05-46b6d5d38b67
-- title:
--   St Piece Root Product Polynomial
-- statement:
--   Definitions and structural lemmas for St Piece Root Product Polynomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/StPieceRootProductPolynomial.lean

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
open MvPolynomial Matrix
def PieceRootProductPolynomial.Statement : Prop :=
  ∀ (n d N k : ℕ) (A : Matrix (Fin d) (Fin n) ℂ) (Z : Set (Fin n → ℂ)) (c : Fin n → ℂ)
    (m : Polynomial (MvPolynomial (Fin d) ℂ)) (Q : MvPolynomial (Fin d) ℂ) (O F : Set (Fin n → ℂ)),
    m.Monic → Q ≠ 0 →
    (∀ x ∈ Z, (m.map (eval (A *ᵥ x))).IsRoot (∑ j, c j * x j)) →
    (∀ y : Fin d → ℂ, eval y Q ≠ 0 →
      {x | x ∈ Z ∧ A *ᵥ x = y}.Finite ∧ {x | x ∈ Z ∧ A *ᵥ x = y}.ncard = N ∧
      ∀ x ∈ Z, A *ᵥ x = y → ∃ (U : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
        (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen U ∧ y ∈ U ∧ IsOpen V ∧ x ∈ V ∧
          DifferentiableOn ℂ g U ∧ g y = x ∧ (∀ w ∈ U, A *ᵥ g w = w) ∧ Z ∩ V = g '' U) →
    IsOpen O → IsClosed F →
    {x | x ∈ Z ∧ eval (A *ᵥ x) Q ≠ 0} ∩ O = {x | x ∈ Z ∧ eval (A *ᵥ x) Q ≠ 0} ∩ F →
    (∀ y : Fin d → ℂ, eval y Q ≠ 0 → {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y}.ncard = k) →
    ∃ G : Polynomial (MvPolynomial (Fin d) ℂ), G.Monic ∧ G.natDegree = k ∧
      ∀ y : Fin d → ℂ, eval y Q ≠ 0 →
        G.map (eval y) = ∏ᶠ x ∈ {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y},
          (Polynomial.X - Polynomial.C (∑ j, c j * x j))
end GroundTheory.Heights₂.Heights.HilbertSamuel


