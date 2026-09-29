-- Prove2me | solution 1 for AutomorphicForm.exists_finset_convOp_convOp_eq_sum_on_isotypicCuspSubmodule_inf_archCutSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/672cca9b-5c34-5766-a865-c2797f937cc8

import Theorems.Thm_AutomorphicForm_convOp_convOp_eq_convOp_of_eq_integral_mul_comp_inv_mul
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_finset_convOp_convOp_eq_sum_on_isotypicCuspSubmodule_inf_archCutSubmodule
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm

private theorem isFactorizableTestFn_of_isUnitFactorizableAbove {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] {U : Subgroup (AdelicGL2 (𝓞 L) L)} {S : Finset (HeightOneSpectrum (𝓞 K))}
    {φ : AdelicGL2 (𝓞 L) L → ℂ} (h : IsUnitFactorizableAbove K L U S φ) : IsFactorizableTestFn L φ := by
  obtain ⟨-, φa, φf, φS, hfa, hff, -, -, -, heq⟩ := h
  exact ⟨φa, φf, hfa, hff, heq⟩

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) (hd : d₁ < d₂)
    (hcov : CoversModCentre L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂))
    (ξ : (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)).Z →* ℂˣ)
    (NK : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (Ψ : HeckeEigensystem L ℂ) (tys : ArchTypeFamily L)
    (φ ψ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφ : IsUnitFactorizableAboveOfType K L tys
        (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK φ ∧
      Continuous φ ∧ HasCompactSupport φ)
    (hψ : IsUnitFactorizableAboveOfType K L tys
        (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK ψ ∧
      Continuous ψ ∧ HasCompactSupport ψ) :
    ∃ (s : Finset (AdelicGL2 (𝓞 L) L → ℂ)) (a : (AdelicGL2 (𝓞 L) L → ℂ) → ℂ),
      (∀ φ ∈ s, IsUnitFactorizableAboveOfType K L tys
          (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK φ ∧
        Continuous φ ∧ HasCompactSupport φ) ∧
        ∀ w ∈ isotypicCuspSubmodule L
          (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ
        ⊓ archCutSubmodule L tys,
          convOp L ψ (convOp L φ w) = ∑ χ ∈ s, a χ • convOp L χ w := by
  have _ := hd
  have _ := hcov
  have _ := hNS
  obtain ⟨hφt, hφc, hφs⟩ := hφ
  obtain ⟨hψt, hψc, hψs⟩ := hψ
  set χ : AdelicGL2 (𝓞 L) L → ℂ := fun g => ∫ y, ψ y * φ (y⁻¹ * g) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) with hχ
  obtain ⟨⟨-, hχc, hχs⟩, hconv, -, -, hleft, hright, hunit⟩ :=
    AutomorphicForm.convOp_convOp_eq_convOp_of_eq_integral_mul_comp_inv_mul K L
      (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK φ ψ
      ⟨isFactorizableTestFn_of_isUnitFactorizableAbove hφt.1, hφc, hφs⟩
      ⟨isFactorizableTestFn_of_isUnitFactorizableAbove hψt.1, hψc, hψs⟩ χ hχ
  refine ⟨{χ}, fun _ => 1, ?_, ?_⟩
  · intro χ' hχ'
    rw [Finset.mem_singleton] at hχ'
    subst hχ'
    exact ⟨⟨hunit hψt.1 hφt.1, hleft tys hψt.2.1, hright tys hφt.2.2⟩, hχc, hχs⟩
  · intro w hw
    simp only [Finset.sum_singleton, one_smul]
    exact hconv w (continuous_of_mem_isotypicCuspSubmodule_inf L w hw)

#print axioms solution

end S_AutomorphicForm_exists_finset_convOp_convOp_eq_sum_on_isotypicCuspSubmodule_inf_archCutSubmodule
end P2MW
export P2MW.S_AutomorphicForm_exists_finset_convOp_convOp_eq_sum_on_isotypicCuspSubmodule_inf_archCutSubmodule (solution)
