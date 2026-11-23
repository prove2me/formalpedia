-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_TrFormBaseChangeNondegenerate
-- name    : Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_TrFormBaseChangeNondegenerate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:53.868405+00:00
-- url     : https://prove2.me/theorems/186d7af4-3a10-4542-8986-884015d09095
-- title:
--   Tr Form Base Change Nondegenerate
-- statement:
--   Definitions and structural lemmas for Tr Form Base Change Nondegenerate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/TrFormBaseChangeNondegenerate.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_OneAddZeta21PowSevenAddPowFourteenEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Theorems.Thm_GlobalTheory_HostModel_finrank_rat_E21_eq_twelve
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven


set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HostModel
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
def trForm (H : Host E) : LinearMap.BilinForm ℤ (𝓞 E) :=
  ((LinearMap.mul ℤ (𝓞 E)).compr₂ (Algebra.trace ℤ (𝓞 E))) ∘ₗ H.bar.toAddEquiv.toIntLinearEquiv.toLinearMap
theorem trForm_apply (H : Host E) (x y : 𝓞 E) : trForm H x y = Algebra.trace ℤ (𝓞 E) (H.bar x * y) := rfl
theorem embedding_bar (H : Host E) (τ : E →+* ℂ) (a : 𝓞 E) : τ (H.bar a : 𝓞 E) = conj (τ a) := by
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
omit [IsCMField E] in

theorem coe_trace_eq_sum (a : 𝓞 E) : (Algebra.trace ℤ (𝓞 E) a : ℂ) = ∑ τ : E →+* ℂ, τ a := by
  have h : (Algebra.trace ℤ (𝓞 E) a : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ E (a : E)) := by
    rw [← Algebra.coe_trace_int]; simp
  rw [h, trace_eq_sum_embeddings ℂ]
  exact (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _ fun _ => rfl).symm
theorem trForm_eq_sum (H : Host E) (x y : 𝓞 E) : (trForm H x y : ℂ) = ∑ τ : E →+* ℂ, conj (τ x) * τ y := by
  rw [trForm_apply, coe_trace_eq_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← embedding_bar H, ← map_mul]; rfl
theorem trForm_self_eq_sum (H : Host E) (y : 𝓞 E) : (trForm H y y : ℝ) = ∑ τ : E →+* ℂ, ‖τ y‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  rw [trForm_eq_sum]
  exact Finset.sum_congr rfl fun τ _ => Complex.conj_mul' _
theorem trForm_one_one (H : Host E) : trForm H 1 1 = Module.finrank ℚ E := by
  apply Int.cast_injective (α := ℝ)
  rw [trForm_self_eq_sum]
  simp [Embeddings.card]
def realEmb (τ : E →+* ℂ) : ℝ ⊗[ℤ] 𝓞 E →ₐ[ℝ] ℂ :=
  Algebra.TensorProduct.lift (Algebra.ofId ℝ ℂ) (τ.comp (algebraMap (𝓞 E) E)).toIntAlgHom
    fun _ _ => Commute.all _ _
omit [NumberField E] [IsCMField E] in

@[simp] theorem realEmb_tmul (τ : E →+* ℂ) (r : ℝ) (a : 𝓞 E) : realEmb τ (r ⊗ₜ a) = r * τ a := rfl
theorem trForm_rt_rt (H : Host E) : trForm H H.rt H.rt = H.d * Module.finrank ℚ E := by
  have h : H.bar H.rt * H.rt = (H.d : ℤ) • (H.bar 1 * 1) := by
    rw [bar_rt, map_one]
    simp only [mul_one, zsmul_eq_mul, Int.cast_natCast]
    linear_combination -H.rt_sq
  rw [trForm_apply, h, map_smul, ← trForm_apply, trForm_one_one, smul_eq_mul]
example : trForm host 1 1 = 12 := by
  rw [trForm_one_one, finrank_rat_E21_eq_twelve]; rfl
example : trForm host host.rt host.rt = 84 := by
  rw [trForm_rt_rt, finrank_rat_E21_eq_twelve, host_d]; rfl
example : Algebra.trace ℤ (𝓞 E21) (host.rt * host.rt) = -84 := by
  have h := trForm_rt_rt host
  rw [trForm_apply, bar_rt, neg_mul, map_neg, finrank_rat_E21_eq_twelve, host_d] at h
  omega
end GlobalTheory.HostModel
end


