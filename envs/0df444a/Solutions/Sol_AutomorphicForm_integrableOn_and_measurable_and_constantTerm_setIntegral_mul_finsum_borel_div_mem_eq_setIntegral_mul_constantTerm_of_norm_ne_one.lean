-- Prove2me | solution 1 for AutomorphicForm.integrableOn_and_measurable_and_constantTerm_setIntegral_mul_finsum_borel_div_mem_eq_setIntegral_mul_constantTerm_of_norm_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/9c5d0c40-6f34-581e-bd37-e095a6b7c6bd

import Mathlib
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_integrable_and_integral_finsum_borel_div_mem_inv_unipotentGL2_mul_eq_integral_finsum_of_norm_ne_one
import Theorems.Thm_AutomorphicForm_integrableOn_and_measurable_and_constantTerm_setIntegral_mul_finsum_borel_div_mem_eq_setIntegral_mul_integral_finsum_inv_unipotentGL2_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integrableOn_and_measurable_and_constantTerm_setIntegral_mul_finsum_borel_div_mem_eq_setIntegral_mul_constantTerm_of_norm_ne_one
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (A : Set L) (hA : ∀ ρ ∈ A, Algebra.norm K ρ ≠ 1)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    (∀ x : AutomorphicForm.AdelicGL2 (𝓞 L) L,
      IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL) ∧
    (∀ x : AutomorphicForm.AdelicGL2 (𝓞 L) L,
      IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        @AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
          (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
              (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
                (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ * AutomorphicForm.sigmaAdelicAct K L D σ y))
          (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ΩL νZL) ∧
    Measurable (fun x : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL) ∧
    Measurable (fun x : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        @AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
          (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
              (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
                (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ * AutomorphicForm.sigmaAdelicAct K L D σ y))
          (AutomorphicForm.centralScalar (𝓞 L) L z * x) ∂νZL) ∧
    ∀ x : AutomorphicForm.AdelicGL2 (𝓞 L) L,
      @AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
          (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun x' : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
            ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
                  (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
                φ (x'⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
                  AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x')) ∂νZL)
          x =
        ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          @AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
            (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
            (fun t => AutomorphicForm.unipotentGL2 t)
            (fun y => ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
                (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
                  (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ * AutomorphicForm.sigmaAdelicAct K L D σ y))
            (AutomorphicForm.centralScalar (𝓞 L) L z * x) ∂νZL := by

  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    AutomorphicForm.integrableOn_and_measurable_and_constantTerm_setIntegral_mul_finsum_borel_div_mem_eq_setIntegral_mul_integral_finsum_inv_unipotentGL2_mul
      K L νZL ΩL hΩL D σ ξL hξc hξt A φ hφc hφs
  refine ⟨h1, h2, h3, h4, fun x => ?_⟩

  rw [h5 x]

  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * _ = ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * _
  congr 1
  exact (AutomorphicForm.integrable_and_integral_finsum_borel_div_mem_inv_unipotentGL2_mul_eq_integral_finsum_of_norm_ne_one
    K L D σ hgen A hA φ hφc hφs x (AutomorphicForm.centralScalar (𝓞 L) L z * x)).2.2

end S_AutomorphicForm_integrableOn_and_measurable_and_constantTerm_setIntegral_mul_finsum_borel_div_mem_eq_setIntegral_mul_constantTerm_of_norm_ne_one
end P2MW
export P2MW.S_AutomorphicForm_integrableOn_and_measurable_and_constantTerm_setIntegral_mul_finsum_borel_div_mem_eq_setIntegral_mul_constantTerm_of_norm_ne_one (solution)
