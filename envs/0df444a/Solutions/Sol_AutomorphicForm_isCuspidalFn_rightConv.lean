-- Prove2me | solution 1 for AutomorphicForm.isCuspidalFn_rightConv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/58554a28-f436-5f2d-996e-4ac6b07612dd

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isCuspidalFn_rightConv
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicBox NumberField.AdelicLevel NumberField.AdelicHaar MeasureTheory
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_isCuspidalFn_rightConv.AutomorphicForm"

section Core
p2m_open "MeasureTheory AutomorphicForm P2MW.S_AutomorphicForm_isCuspidalFn_rightConv.AutomorphicForm"
p2m_open "MeasureTheory AutomorphicForm P2MW.S_AutomorphicForm_isCuspidalFn_rightConv.AutomorphicForm"
namespace AutomorphicForm p2m_export "AutomorphicForm" "rightConv IsFactorizableTestFn productionPinsOf AdelicGL2 unipotentGL2 constantTermIntegrand constantTerm IsCuspidalFn continuous_unipotentGL2 continuous_and_hasCompactSupport_of_isFactorizableTestFn" namespace G2Aux end AutomorphicForm.G2Aux
p2m_open_scoped "AutomorphicForm" in

theorem AutomorphicForm.G2Aux.constantTerm_eq_zero_of_eq_integral_kernel
    {Q : Type*} [MeasurableSpace Q] (ν : Measure Q) [SFinite ν]
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    {G : Type*} [Group G] (u : Q → G) (r : X → G) (k : X → ℂ) (ψ Ψ : G → ℂ)
    (hψ : IsCuspidalFn ν u ψ)
    (hΨ : ∀ h : G, Ψ h = ∫ x, k x * ψ (h * r x) ∂μ)
    (g : G)
    (hint : Integrable (fun p : Q × X => k p.2 * ψ (u p.1 * g * r p.2)) (ν.prod μ)) :
    constantTerm ν u Ψ g = 0 := by
  simp only [constantTerm, constantTermIntegrand, hΨ]
  have hswap := MeasureTheory.integral_integral_swap (f := fun q x => k x * ψ (u q * g * r x)) hint
  rw [hswap]
  have h0 : ∀ x : X, ∫ q, k x * ψ (u q * g * r x) ∂ν = 0 := fun x => by
    rw [integral_const_mul]
    simp_rw [mul_assoc]
    have := hψ (g * r x)
    simp only [constantTerm, constantTermIntegrand] at this
    rw [this, mul_zero]
  simp [h0]
end Core

theorem solution
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hcont : Continuous φ)
    (hcusp : @IsCuspidalFn _ (productionPinsOf F D U gen (adelicBox F)).nS _ _
      (productionPinsOf F D U gen (adelicBox F)).ν unipotentGL2 φ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    @IsCuspidalFn _ (productionPinsOf F D U gen (adelicBox F)).nS _ _
      (productionPinsOf F D U gen (adelicBox F)).ν unipotentGL2 (rightConv F φ f) := by

  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology F
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicAddHaar (𝓞 F) F).IsAddHaarMeasure := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI : SigmaFinite (adelicGLHaar (Fin 2) (𝓞 F) F) := inferInstance
  set ν := ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F) with hν
  haveI : IsProbabilityMeasure ν := NumberField.AdelicBox.isProbabilityMeasure_cond_adelicBox F
  change IsCuspidalFn ν unipotentGL2 (rightConv F φ f)
  have hcusp' : IsCuspidalFn ν unipotentGL2 φ := hcusp
  obtain ⟨hfc, hfs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf
  intro g
  refine AutomorphicForm.G2Aux.constantTerm_eq_zero_of_eq_integral_kernel ν (adelicGLHaar (Fin 2) (𝓞 F) F)
    unipotentGL2 id f φ (rightConv F φ f) hcusp' (fun h => ?_) g ?_
  · simp only [rightConv, id]
    exact integral_congr_ae (ae_of_all _ fun y => mul_comm _ _)

  obtain ⟨Cb, hCb, hboxCb⟩ := NumberField.AdelicBox.exists_isCompact_adelicBox_subset F
  have hmap : Continuous fun p : AdeleRing (𝓞 F) F × AdelicGL2 (𝓞 F) F => unipotentGL2 p.1 * g * p.2 :=
    ((continuous_unipotentGL2.comp continuous_fst).mul continuous_const).mul continuous_snd
  obtain ⟨M₀, hM₀⟩ := ((hCb.prod hfs).image hmap).exists_bound_of_continuousOn
    (f := φ) hcont.continuousOn
  set M := max M₀ 0 with hM
  have hMφ : ∀ (q : AdeleRing (𝓞 F) F) (x : AdelicGL2 (𝓞 F) F), q ∈ adelicBox F → x ∈ tsupport f →
      ‖φ (unipotentGL2 q * g * x)‖ ≤ M := fun q x hq hx =>
    (hM₀ _ ⟨(q, x), ⟨hboxCb hq, hx⟩, rfl⟩).trans (le_max_left _ _)

  have hae : ∀ᵐ p ∂(ν.prod (adelicGLHaar (Fin 2) (𝓞 F) F)), p.1 ∈ adelicBox F := by
    have h1 : ∀ᵐ q ∂ν, q ∈ adelicBox F :=
      ProbabilityTheory.ae_cond_mem (NumberField.AdelicBox.measurableSet_adelicBox F)
    exact (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := adelicGLHaar (Fin 2) (𝓞 F) F)).ae h1
  have hfint : Integrable f (adelicGLHaar (Fin 2) (𝓞 F) F) := hfc.integrable_of_hasCompactSupport hfs
  have hf2 : Integrable (fun p : AdeleRing (𝓞 F) F × AdelicGL2 (𝓞 F) F => f p.2)
      (ν.prod (adelicGLHaar (Fin 2) (𝓞 F) F)) := by
    simpa using (integrable_const (1 : ℂ)).mul_prod hfint
  have hcont2 : Continuous fun p : AdeleRing (𝓞 F) F × AdelicGL2 (𝓞 F) F =>
      φ (unipotentGL2 p.1 * g * p.2) := hcont.comp hmap
  refine (hf2.norm.mul_const M).mono' (hf2.aestronglyMeasurable.mul hcont2.aestronglyMeasurable)
    (hae.mono fun p hp => ?_)
  rw [norm_mul, id]
  by_cases hx : p.2 ∈ tsupport f
  · exact mul_le_mul_of_nonneg_left (hMφ p.1 p.2 hp hx) (norm_nonneg _)
  · have : f p.2 = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [this, hM]

end S_AutomorphicForm_isCuspidalFn_rightConv
end P2MW
export P2MW.S_AutomorphicForm_isCuspidalFn_rightConv (solution)
