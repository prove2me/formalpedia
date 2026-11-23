-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_PremisesInhabited
-- name    : Development_AbelianVarietyTheory_Counterexamples_JetSurvey_PremisesInhabited
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:22.778318+00:00
-- url     : https://prove2.me/theorems/90017cc6-318a-4f94-a9e9-c9c5fddcb513
-- title:
--   Premises Inhabited
-- statement:
--   Definitions and structural lemmas for Premises Inhabited, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/PremisesInhabited.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LatticeBoundTests
open NumberField
section Trace
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
def trBil : 𝓞 E →ₗ[ℤ] 𝓞 E →ₗ[ℤ] ℝ :=
  LinearMap.mk₂ ℤ (fun x y => ∑ σ : E →+* ℂ, (σ (x : E) * starRingEnd ℂ (σ (y : E))).re)
    (fun x x' y => by simp [add_mul, Finset.sum_add_distrib])
    (fun k x y => by simp [Finset.mul_sum, mul_assoc, mul_add])
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun k x y => by simp [Finset.mul_sum, mul_add, mul_left_comm])
end Trace
abbrev K₃ := CyclotomicField 3 ℚ
instance isCyc_K₃ : IsCyclotomicExtension {3} ℚ K₃ := CyclotomicField.isCyclotomicExtension 3 ℚ
instance isCMField_K₃ : IsCMField K₃ := IsCyclotomicExtension.Rat.isCMField K₃ (S := {3}) ⟨3, rfl, by norm_num⟩
end GlobalTheory.LatticeBoundTests


