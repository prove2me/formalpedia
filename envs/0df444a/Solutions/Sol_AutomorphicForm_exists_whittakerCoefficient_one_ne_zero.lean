-- Prove2me | solution 1 for AutomorphicForm.exists_whittakerCoefficient_one_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/f08cc5a4-fddd-5aaa-8d3e-1aa1c2b5ce18

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Theorems.Thm_AutomorphicForm_hasSum_whittakerCoefficient
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_AdelicBox_isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_whittakerCoefficient_one_ne_zero
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm

noncomputable section

namespace WhittakerGenericity

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.adeleBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_adeleBorel

private scoped instance : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := by
  have hsurj : Function.Surjective
      (fun β : F => (⟨algebraMap F _ β, β, rfl⟩ : AdeleRing.principalSubgroup (𝓞 F) F)) := by
    rintro ⟨_, β, rfl⟩; exact ⟨β, rfl⟩
  exact hsurj.countable

private theorem exists_coefficient_ne_zero
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hcont : Continuous (fun x => φ (unipotentGL2 x * g)))
    (hsum : Summable (fun α : F =>
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g))
    (hg : φ g ≠ 0) :
    ∃ α : F, whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g ≠ 0 := by
  by_contra h
  push Not at h
  have hD := AutomorphicForm.hasSum_whittakerCoefficient F D U gen ψ hψ φ g hcont hsum
  have h0 : HasSum (fun α : F =>
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g) 0 := by
    simp only [h]
    exact hasSum_zero
  exact hg (hD.unique h0)

private theorem globalPoints_coe_apply (γ : Matrix.GeneralLinearGroup (Fin 2) F) (i j : Fin 2) :
    (globalPoints (𝓞 F) F γ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j
      = algebraMap F (AdeleRing (𝓞 F) F) ((γ : Matrix (Fin 2) (Fin 2) F) i j) := rfl

private def diagGL2 (α : F) (hα : α ≠ 0) : Matrix.GeneralLinearGroup (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![α, 0; 0, 1] (by simp [Matrix.det_fin_two_of, hα])

private theorem unipotentGL2_mul_globalPoints_diagGL2 (α : F) (hα : α ≠ 0) (x : AdeleRing (𝓞 F) F) :
    unipotentGL2 x * globalPoints (𝓞 F) F (diagGL2 F α hα)
      = globalPoints (𝓞 F) F (diagGL2 F α hα)
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) α⁻¹ * x) := by
  have hinv : algebraMap F (AdeleRing (𝓞 F) F) α * algebraMap F (AdeleRing (𝓞 F) F) α⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hα, map_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [globalPoints_coe_apply, diagGL2, Matrix.mul_apply, Fin.sum_univ_two, ← mul_assoc, hinv]

private theorem globalPoints_unipotentGL2 (β : F) :
    globalPoints (𝓞 F) F (unipotentGL2 β) = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [globalPoints_coe_apply]

private theorem integrand_vadd (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (α : F) (g : AdelicGL2 (𝓞 F) F) (γ : AdeleRing.principalSubgroup (𝓞 F) F)
    (x : AdeleRing (𝓞 F) F) :
    φ (unipotentGL2 (γ +ᵥ x) * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * (γ +ᵥ x)))
      = φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)) := by
  obtain ⟨_, β, rfl⟩ := γ
  have hv : ((⟨algebraMap F _ β, β, rfl⟩ : AdeleRing.principalSubgroup (𝓞 F) F) +ᵥ x)
      = algebraMap F (AdeleRing (𝓞 F) F) β + x := rfl
  rw [hv]
  congr 1
  · rw [unipotentGL2_add, mul_assoc, ← globalPoints_unipotentGL2, hleft]
  · rw [mul_add, neg_add, ψ.map_add_eq_mul]
    have h1 :
        ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * algebraMap F (AdeleRing (𝓞 F) F) β)) = 1 := by
      rw [← map_mul, ← map_neg]
      exact hψ.principalInvariant (-(α * β))
    rw [h1, one_mul]

private def principalIdeleOf (a : Fˣ) : (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a

private theorem principalIdeleOf_smul (a : Fˣ) (x : AdeleRing (𝓞 F) F) :
    principalIdeleOf F a • x = algebraMap F (AdeleRing (𝓞 F) F) (a : F) * x := rfl

private theorem distribHaarChar_principalIdeleOf (a : Fˣ) :
    distribHaarChar (AdeleRing (𝓞 F) F) (principalIdeleOf F a) = 1 :=
  NumberField.AdeleRing.distribHaarChar_algebraMap F a

private theorem measurePreserving_principalIdeleOf_smul (a : Fˣ) :
    MeasurePreserving (fun x : AdeleRing (𝓞 F) F => principalIdeleOf F a • x)
      (adelicAddHaar (𝓞 F) F) (adelicAddHaar (𝓞 F) F) := by
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  haveI : (adelicAddHaar (𝓞 F) F).Regular := Measure.regular_addHaarMeasure
  have hmeas : Measurable (fun x : AdeleRing (𝓞 F) F => principalIdeleOf F a • x) := by
    simp only [principalIdeleOf_smul]
    exact (continuous_const.mul continuous_id).measurable
  refine ⟨hmeas, ?_⟩
  ext s hs
  rw [Measure.map_apply hmeas hs, Set.preimage_smul,
    ← distribHaarChar_mul (adelicAddHaar (𝓞 F) F) (principalIdeleOf F a)⁻¹ s]
  have h1 : distribHaarChar (AdeleRing (𝓞 F) F) (principalIdeleOf F a)⁻¹ = 1 := by
    rw [map_inv, distribHaarChar_principalIdeleOf, inv_one]
  rw [h1, ENNReal.coe_one, one_mul]

private theorem measurableEmbedding_principalIdeleOf_smul (a : Fˣ) :
    MeasurableEmbedding (fun x : AdeleRing (𝓞 F) F => principalIdeleOf F a • x) :=
  (Homeomorph.smul (α := AdeleRing (𝓞 F) F) (principalIdeleOf F a)).measurableEmbedding

private theorem whittakerCoefficient_productionPinsOf_eq
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F)
    (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g
      = ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹.toReal •
          ∫ x in adelicBox F,
            φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))
              ∂(adelicAddHaar (𝓞 F) F) := by
  show (∫ x, φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))
      ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))) = _
  unfold ProbabilityTheory.cond
  rw [integral_smul_measure]

private theorem image_principalIdeleOf_inv_smul_adelicBox (α : F) (hα : α ≠ 0) :
    (fun x : AdeleRing (𝓞 F) F => principalIdeleOf F (Units.mk0 α hα)⁻¹ • x) '' adelicBox F
      = (fun x : AdeleRing (𝓞 F) F => algebraMap F (AdeleRing (𝓞 F) F) α * x) ⁻¹' adelicBox F := by
  refine congrFun (Set.image_eq_preimage_of_inverse ?_ ?_) (adelicBox F)
  · intro x
    simp only [principalIdeleOf_smul, Units.val_inv_eq_inv_val, Units.val_mk0, ← mul_assoc,
      ← map_mul, mul_inv_cancel₀ hα, map_one, one_mul]
  · intro x
    simp only [principalIdeleOf_smul, Units.val_inv_eq_inv_val, Units.val_mk0, ← mul_assoc,
      ← map_mul, inv_mul_cancel₀ hα, map_one, one_mul]

private theorem whittakerCoefficient_eq_one_diagGL2_mul
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (α : F) (hα : α ≠ 0) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g
      = whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1
          (globalPoints (𝓞 F) F (diagGL2 F α hα) * g) := by
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  rw [whittakerCoefficient_productionPinsOf_eq, whittakerCoefficient_productionPinsOf_eq]

  have hpt : ∀ x : AdeleRing (𝓞 F) F,
      φ (unipotentGL2 x * (globalPoints (𝓞 F) F (diagGL2 F α hα) * g))
          * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) 1 * x))
        = φ (unipotentGL2 (principalIdeleOf F (Units.mk0 α hα)⁻¹ • x) * g)
          * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α
                * (principalIdeleOf F (Units.mk0 α hα)⁻¹ • x))) := by
    intro x
    simp only [principalIdeleOf_smul, Units.val_inv_eq_inv_val, Units.val_mk0, map_one, one_mul]
    rw [← mul_assoc, unipotentGL2_mul_globalPoints_diagGL2 F α hα x, mul_assoc, hleft]
    have hx :
        algebraMap F (AdeleRing (𝓞 F) F) α * (algebraMap F (AdeleRing (𝓞 F) F) α⁻¹ * x) = x := by
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hα, map_one, one_mul]
    rw [hx]

  have himg := (measurePreserving_principalIdeleOf_smul F (Units.mk0 α hα)⁻¹).setIntegral_image_emb
    (measurableEmbedding_principalIdeleOf_smul F (Units.mk0 α hα)⁻¹)
    (fun y => φ (unipotentGL2 y * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * y))) (adelicBox F)
  have hFD : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F)
      ((fun x : AdeleRing (𝓞 F) F => principalIdeleOf F (Units.mk0 α hα)⁻¹ • x) '' adelicBox F)
      (adelicAddHaar (𝓞 F) F) := by
    rw [image_principalIdeleOf_inv_smul_adelicBox F α hα]
    exact NumberField.AdelicBox.isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox F
      (adelicAddHaar (𝓞 F) F) α hα
  have hdom := (isAddFundamentalDomain_adelicBox_adelicAddHaar F).setIntegral_eq hFD
    (f := fun y => φ (unipotentGL2 y * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * y)))
    (fun γ x => integrand_vadd F ψ hψ φ hleft α g γ x)
  have hint :
      (∫ x in adelicBox F, φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))
          ∂(adelicAddHaar (𝓞 F) F))
        = ∫ x in adelicBox F,
            φ (unipotentGL2 x * (globalPoints (𝓞 F) F (diagGL2 F α hα) * g))
              * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) 1 * x)) ∂(adelicAddHaar (𝓞 F) F) := by
    rw [funext hpt]
    exact hdom.trans himg
  rw [hint]

private theorem genericity_one
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (g₀ : AdelicGL2 (𝓞 F) F)
    (hcusp : whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 0 g₀ = 0)
    (hcont : Continuous (fun x => φ (unipotentGL2 x * g₀)))
    (hsum : Summable (fun α : F =>
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g₀))
    (hg₀ : φ g₀ ≠ 0) :
    ∃ g : AdelicGL2 (𝓞 F) F,
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1 g ≠ 0 := by
  obtain ⟨α, hα⟩ := exists_coefficient_ne_zero F D U gen ψ hψ φ g₀ hcont hsum hg₀
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact hα hcusp
  refine ⟨globalPoints (𝓞 F) F (diagGL2 F α hα0) * g₀, ?_⟩
  rw [← whittakerCoefficient_eq_one_diagGL2_mul F D U gen ψ hψ φ hleft α hα0 g₀]
  exact hα

end WhittakerGenericity
p2m_reactivate "P2MW.S_AutomorphicForm_exists_whittakerCoefficient_one_ne_zero.WhittakerGenericity"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_whittakerCoefficient_one_ne_zero.WhittakerGenericity"

theorem solution
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (g₀ : AdelicGL2 (𝓞 F) F)
    (hcusp : whittakerCoefficient F (productionPinsOf F D U gen (AdelicBox.adelicBox F)) ψ φ 0 g₀
      = 0)
    (hcont : Continuous (fun x => φ (unipotentGL2 x * g₀)))
    (hsum : Summable (fun α : F =>
      whittakerCoefficient F (productionPinsOf F D U gen (AdelicBox.adelicBox F)) ψ φ α g₀))
    (hg₀ : φ g₀ ≠ 0) :
    ∃ g : AdelicGL2 (𝓞 F) F,
      whittakerCoefficient F (productionPinsOf F D U gen (AdelicBox.adelicBox F)) ψ φ 1 g ≠ 0 :=
  WhittakerGenericity.genericity_one F D U gen ψ hψ φ hleft g₀ hcusp hcont hsum hg₀

#print axioms solution

end S_AutomorphicForm_exists_whittakerCoefficient_one_ne_zero
end P2MW
export P2MW.S_AutomorphicForm_exists_whittakerCoefficient_one_ne_zero (solution)
