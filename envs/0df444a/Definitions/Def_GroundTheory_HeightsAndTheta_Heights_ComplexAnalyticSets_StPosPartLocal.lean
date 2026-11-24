-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPosPartLocal
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPosPartLocal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:59:31.56696+00:00
-- url     : https://prove2.me/theorems/a7f49320-a78c-47f9-9fae-4b4e020907d8
-- title:
--   St Pos Part Local
-- statement:
--   Definitions and structural lemmas for St Pos Part Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPosPartLocal.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPosPartIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory ComplexSets
noncomputable section
def PosPartLocal.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A A' : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (x : Fin n → ℂ),
    Measurable f → (∀ k, SmoothNear (zeroSet J) (φ k)) →
    (∃ s, IsSheetAt J A x s) → (∃ s', IsSheetAt J A' x s') →
      ∃ W : Set (Fin n → ℂ), IsOpen W ∧ x ∈ W ∧
        ∀ E : Set (Fin n → ℂ), MeasurableSet E → E ⊆ W →
          ∫⁻ y, ENNReal.ofReal (chartPosDens J A (E.indicator f) φ y) =
            ∫⁻ y, ENNReal.ofReal (chartPosDens J A' (E.indicator f) φ y)
end
end GroundTheory.Heights₂.Heights


