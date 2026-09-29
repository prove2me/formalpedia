-- Prove2me | solution 1 for AutomorphicForm.continuous_rightConv_of_continuous_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/3a26f3f5-aebf-5166-90f8-3ff4f4b745cc

import Definitions.Def_AutomorphicForm_RightConvolution
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_continuous_rightConv_of_continuous_of_hasCompactSupport
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    (F : Type) [Field F] [NumberField F]
    (φ : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) (hφ : Continuous φ)
    (g : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Continuous (AutomorphicForm.rightConv F φ g) := by
  haveI : BorelSpace (GL (Fin 2) (AdeleRing (𝓞 F) F)) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI : SecondCountableTopology (GL (Fin 2) (AdeleRing (𝓞 F) F)) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  have hcont : Continuous (Function.uncurry fun (x y : GL (Fin 2) (AdeleRing (𝓞 F) F)) => φ (x * y) * g y) :=
    (hφ.comp continuous_mul).mul (hg.comp continuous_snd)
  have h := continuous_parametric_integral_of_continuous
    (μ := NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) hcont hgc.isCompact
  have heq : AutomorphicForm.rightConv F φ g =
      fun x => ∫ y in tsupport g, φ (x * y) * g y ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
    funext x
    rw [AutomorphicForm.rightConv_apply]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]).symm
  rw [heq]
  exact h

end S_AutomorphicForm_continuous_rightConv_of_continuous_of_hasCompactSupport
end P2MW
export P2MW.S_AutomorphicForm_continuous_rightConv_of_continuous_of_hasCompactSupport (solution)
