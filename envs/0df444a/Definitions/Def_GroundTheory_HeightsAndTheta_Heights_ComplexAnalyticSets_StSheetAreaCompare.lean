-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetAreaCompare
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetAreaCompare
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:48.283875+00:00
-- url     : https://prove2.me/theorems/61c81d5e-468b-4c2c-bce8-f1e2868260e2
-- title:
--   St Sheet Area Compare
-- statement:
--   Definitions and structural lemmas for St Sheet Area Compare, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSheetAreaCompare.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetComass
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
open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ENNReal
noncomputable section
def SheetAreaCompare.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ),
    ∃ c : ℝ≥0∞, c < ⊤ ∧ ∀ h : (Fin n → ℂ) → ℝ, Measurable h →
      ∫⁻ y, ‖sheetSum J A (fun x s => |h x| * sheetJac s (A *ᵥ x)) y‖ₑ ≤
        c * ∫⁻ z in zeroSetEuc J, ‖h (WithLp.ofLp z)‖ₑ ∂(μH[((2 * d : ℕ) : ℝ)])
end
end GroundTheory.Heights₂.Heights


