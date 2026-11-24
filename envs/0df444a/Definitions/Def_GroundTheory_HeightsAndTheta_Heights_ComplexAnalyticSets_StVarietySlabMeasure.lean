-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietySlabMeasure
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietySlabMeasure
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:53.479711+00:00
-- url     : https://prove2.me/theorems/b3293e53-5363-4fb9-8300-ade822171f53
-- title:
--   St Variety Slab Measure
-- statement:
--   Definitions and structural lemmas for St Variety Slab Measure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StVarietySlabMeasure.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
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
open MvPolynomial MeasureTheory
open scoped ENNReal
noncomputable section
def VarietySlabMeasure.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ d → linForm u ∉ J → ∀ R : ℝ,
      ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        μH[((2 * d : ℕ) : ℝ)] {z | z ∈ zeroSetEuc J ∧ ‖z‖ ≤ R ∧ ‖∑ j, u j * z j‖ ≤ ε} ≤
          ENNReal.ofReal (C * ε ^ α)
end
end GroundTheory.Heights₂.Heights


