-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPieceCoefficientsHolomorphic
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPieceCoefficientsHolomorphic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:01.19816+00:00
-- url     : https://prove2.me/theorems/872b0058-d650-49ae-95e0-81700be8e6db
-- title:
--   St Piece Coefficients Holomorphic
-- statement:
--   Definitions and structural lemmas for St Piece Coefficients Holomorphic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/StPieceCoefficientsHolomorphic.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPieceRootProductPolynomial
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
def PieceCoefficientsHolomorphic.Statement : Prop :=
  ∀ (n d N : ℕ) (A : Matrix (Fin d) (Fin n) ℂ) (Z : Set (Fin n → ℂ)) (c : Fin n → ℂ)
    (Q : MvPolynomial (Fin d) ℂ) (O F : Set (Fin n → ℂ)),
    (∀ y : Fin d → ℂ, eval y Q ≠ 0 →
      {x | x ∈ Z ∧ A *ᵥ x = y}.Finite ∧ {x | x ∈ Z ∧ A *ᵥ x = y}.ncard = N ∧
      ∀ x ∈ Z, A *ᵥ x = y → ∃ (U : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
        (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen U ∧ y ∈ U ∧ IsOpen V ∧ x ∈ V ∧
          DifferentiableOn ℂ g U ∧ g y = x ∧ (∀ w ∈ U, A *ᵥ g w = w) ∧ Z ∩ V = g '' U) →
    IsOpen O → IsClosed F →
    {x | x ∈ Z ∧ eval (A *ᵥ x) Q ≠ 0} ∩ O = {x | x ∈ Z ∧ eval (A *ᵥ x) Q ≠ 0} ∩ F →
    ∀ i : ℕ, DifferentiableOn ℂ
      (fun y : Fin d → ℂ => (∏ᶠ x ∈ {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y},
        (Polynomial.X - Polynomial.C (∑ j, c j * x j))).coeff i) {y | eval y Q ≠ 0}
end GroundTheory.Heights₂.Heights.HilbertSamuel


