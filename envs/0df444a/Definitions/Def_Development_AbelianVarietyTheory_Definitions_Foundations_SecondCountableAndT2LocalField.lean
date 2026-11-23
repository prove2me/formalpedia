-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:16.125608+00:00
-- url     : https://prove2.me/theorems/33ef1b7d-5619-47d0-af7d-906a549a745e
-- title:
--   Second Countable And T2 Local Field
-- statement:
--   Definitions and structural lemmas for Second Countable And T2 Local Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SecondCountableAndT2LocalField.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
namespace GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def ratCircle : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map _ _ (Rat.castHom ℝ).toAddMonoidHom (by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, by simp⟩)
variable [MeasurableSpace k] [BorelSpace k]
end GlobalTheory.SplitWeil.Model


