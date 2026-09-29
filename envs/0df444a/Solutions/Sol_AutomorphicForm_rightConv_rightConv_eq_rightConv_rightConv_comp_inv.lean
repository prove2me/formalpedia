-- Prove2me | solution 1 for AutomorphicForm.rightConv_rightConv_eq_rightConv_rightConv_comp_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/2b2c24d7-f811-5a40-a6c8-d15d068e4b76

import Definitions.Def_AutomorphicForm_RightConvolution
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_rightConv_rightConv_eq_rightConv_rightConv_comp_inv
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open NumberField MeasureTheory AutomorphicForm NumberField.AdelicHaar
open scoped Pointwise

namespace Ws1
namespace L0

theorem main
    (F : Type) [Field F] [NumberField F]
    (φ : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) (hφ : Continuous φ)
    (f h : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ)
    (hfc : Continuous f) (hfs : HasCompactSupport f) (hhc : Continuous h) (hhs : HasCompactSupport h) :
    rightConv F (rightConv F φ f) h = rightConv F φ (rightConv F h fun x => f x⁻¹) := by
  letI : MeasurableSpace (GL (Fin 2) (AdeleRing (𝓞 F) F)) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (GL (Fin 2) (AdeleRing (𝓞 F) F)) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI : SecondCountableTopology (GL (Fin 2) (AdeleRing (𝓞 F) F)) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  set μ := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  funext g

  show (∫ y, (∫ x, φ (g * y * x) * f x ∂μ) * h y ∂μ) = ∫ z, φ (g * z) * (∫ x, h (z * x) * f x⁻¹ ∂μ) ∂μ

  have h1 : ∀ y : GL (Fin 2) (AdeleRing (𝓞 F) F),
      (∫ x, φ (g * y * x) * f x ∂μ) = ∫ x, φ (g * x) * f (y⁻¹ * x) ∂μ := by
    intro y
    rw [← integral_mul_left_eq_self (fun x => φ (g * x) * f (y⁻¹ * x)) y]
    simp only [mul_assoc, inv_mul_cancel_left]
  have h2 : ∀ z : GL (Fin 2) (AdeleRing (𝓞 F) F),
      (∫ x, h (z * x) * f x⁻¹ ∂μ) = ∫ y, h y * f (y⁻¹ * z) ∂μ := by
    intro z
    rw [← integral_mul_left_eq_self (fun y => h y * f (y⁻¹ * z)) z]
    simp only [mul_inv_rev, inv_mul_cancel_right]
  simp_rw [h1, h2, ← integral_mul_const, ← integral_const_mul]

  have hswap := integral_integral_swap (μ := μ) (ν := μ)
    (f := fun y x => φ (g * x) * f (y⁻¹ * x) * h y) ?_
  · calc (∫ y, ∫ x, φ (g * x) * f (y⁻¹ * x) * h y ∂μ ∂μ)
        = ∫ x, ∫ y, φ (g * x) * f (y⁻¹ * x) * h y ∂μ ∂μ := hswap
      _ = ∫ z, ∫ y, φ (g * z) * (h y * f (y⁻¹ * z)) ∂μ ∂μ := by
          refine integral_congr_ae (ae_of_all _ fun z => integral_congr_ae (ae_of_all _ fun y => ?_))
          simp only []
          ring
  ·
    have hcont : Continuous (Function.uncurry fun y x : GL (Fin 2) (AdeleRing (𝓞 F) F) =>
        φ (g * x) * f (y⁻¹ * x) * h y) := by
      refine ((hφ.comp (continuous_const.mul continuous_snd)).mul
        (hfc.comp ((continuous_fst.inv).mul continuous_snd))).mul (hhc.comp continuous_fst)
    have hsupp : HasCompactSupport (Function.uncurry fun y x : GL (Fin 2) (AdeleRing (𝓞 F) F) =>
        φ (g * x) * f (y⁻¹ * x) * h y) := by
      refine HasCompactSupport.intro (hhs.prod (hhs.mul hfs)) ?_
      rintro ⟨y, x⟩ hyx
      simp only [Function.uncurry_apply_pair]
      by_cases hy : y ∈ tsupport h
      · have hx : x ∉ tsupport h * tsupport f := fun hx => hyx ⟨hy, hx⟩
        have hfx : f (y⁻¹ * x) = 0 := by
          by_contra hne
          exact hx ⟨y, hy, y⁻¹ * x, subset_tsupport _ (Function.mem_support.mpr hne), mul_inv_cancel_left y x⟩
        rw [hfx, mul_zero, zero_mul]
      · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
    exact hcont.integrable_of_hasCompactSupport hsupp

end Ws1.L0

theorem solution
    (F : Type) [Field F] [NumberField F]
    (φ : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) (hφ : Continuous φ)
    (f h : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ)
    (hfc : Continuous f) (hfs : HasCompactSupport f) (hhc : Continuous h) (hhs : HasCompactSupport h) :
    rightConv F (rightConv F φ f) h = rightConv F φ (rightConv F h fun x => f x⁻¹) :=
  Ws1.L0.main F φ hφ f h hfc hfs hhc hhs

end S_AutomorphicForm_rightConv_rightConv_eq_rightConv_rightConv_comp_inv
end P2MW
export P2MW.S_AutomorphicForm_rightConv_rightConv_eq_rightConv_rightConv_comp_inv (solution)
