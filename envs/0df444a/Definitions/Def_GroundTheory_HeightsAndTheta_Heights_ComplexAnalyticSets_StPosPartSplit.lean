-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPosPartSplit
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPosPartSplit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:20.449361+00:00
-- url     : https://prove2.me/theorems/a7b48a0c-8a1c-45c6-bfee-2d2d8ff63a0a
-- title:
--   St Pos Part Split
-- statement:
--   Definitions and structural lemmas for St Pos Part Split, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPosPartSplit.lean

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
def PosPartSplit.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (E : ℕ → Set (Fin n → ℂ))
    (y : Fin d → ℂ),
    IsFiniteProjection J A → Pairwise (Function.onFun Disjoint E) →
    (∀ x ∈ fibre J A y, (∃ s, IsSheetAt J A x s) → ∃ k, x ∈ E k) →
      ENNReal.ofReal (chartPosDens J A f φ y) =
        ∑' k, ENNReal.ofReal (chartPosDens J A ((E k).indicator f) φ y)
end
end GroundTheory.Heights₂.Heights


