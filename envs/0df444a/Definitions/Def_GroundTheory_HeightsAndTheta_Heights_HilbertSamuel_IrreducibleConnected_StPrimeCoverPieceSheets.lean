-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPrimeCoverPieceSheets
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPrimeCoverPieceSheets
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:38.335198+00:00
-- url     : https://prove2.me/theorems/b4a6620d-186d-4556-bc95-8b8978d479c8
-- title:
--   St Prime Cover Piece Sheets
-- statement:
--   Definitions and structural lemmas for St Prime Cover Piece Sheets, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/StPrimeCoverPieceSheets.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
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
def PrimeCoverPieceSheets.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), W.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = d → ComplexSets.IsFiniteProjection W A →
      ∃ P : MvPolynomial (Fin d) ℂ, P ≠ 0 ∧ ∀ R : MvPolynomial (Fin d) ℂ, R ≠ 0 →
        ∀ (O F : Set (Fin n → ℂ)) (k : ℕ), IsOpen O → IsClosed F →
          {x | x ∈ ComplexSets.zeroSet W ∧ eval (A *ᵥ x) (P * R) ≠ 0} ∩ O =
            {x | x ∈ ComplexSets.zeroSet W ∧ eval (A *ᵥ x) (P * R) ≠ 0} ∩ F →
          (∀ y : Fin d → ℂ, eval y (P * R) ≠ 0 →
            {x | x ∈ ComplexSets.zeroSet W ∧ x ∈ O ∧ A *ᵥ x = y}.ncard = k) →
          k = 0 ∨ k = ComplexSets.projDegree W A
end GroundTheory.Heights₂.Heights.HilbertSamuel


