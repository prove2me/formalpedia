-- Prove2me | solution 1 for AutomorphicForm.constantTerm_convOp_eq_zero_of_ae_constantTerm_eq_zero_of_isAutomorphicFnAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/c65dfe44-ad3f-5fcf-9be5-734a109ad08b

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt

import Theorems.Thm_AutomorphicForm_aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_memLp_two_restrict_of_isCompact_of_isAutomorphicFnAt_canonicalTruncationDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_constantTerm_convOp_eq_zero_of_ae_constantTerm_eq_zero_of_isAutomorphicFnAt
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

namespace Ws31
namespace T6A

p2m_open "AutomorphicForm~continuous_unipotentGL2"

theorem continuous_unipotentGL2 {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (fun a : A => (unipotentGL2 a : GL (Fin 2) A)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun a : A => ((unipotentGL2 a : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2] <;> first | exact continuous_const | exact continuous_id
  · show Continuous fun a : A => (((unipotentGL2 a)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)
    have : (fun a : A => (((unipotentGL2 a)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)) = fun a => !![1, -a; 0, 1] := by
      funext a; rfl
    rw [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact continuous_neg | exact continuous_id.neg

end Ws31.T6A

p2m_open "AutomorphicForm~continuous_unipotentGL2" in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (u : AdelicGL2 (𝓞 K) K → ℂ) (_hu : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
    :
    letI := adeleBorel (𝓞 K) K
    (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 u g = 0) →
    ∀ g : AdelicGL2 (𝓞 K) K, constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 (convOp K f u) g = 0 := by
  intro hCT g
  classical
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 K) K

  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set ν : Measure (AdeleRing (𝓞 K) K) := (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν with hν
  have hνdef : ν = ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K) := rfl
  haveI : IsProbabilityMeasure ν := by rw [hνdef]; exact isProbabilityMeasure_cond_adelicBox K

  obtain ⟨-, -, -, hslab, hFD⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  have hmeas : AEStronglyMeasurable u μ :=
    AutomorphicForm.aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab K α β hα hαβ
      (AutomorphicForm.canonicalTruncationDomain K α β) hslab hFD ξK u _hu

  set t : AdeleRing (𝓞 K) K → AdelicGL2 (𝓞 K) K := fun a => unipotentGL2 a * g with ht
  have htc : Continuous t := Ws31.T6A.continuous_unipotentGL2.mul continuous_const

  have hae : ∀ᵐ x ∂μ, (∫ a, u (t a * x) ∂ν) = 0 := by
    have h := (MeasureTheory.eventually_mul_left_iff μ g
      (p := fun y => constantTerm ν unipotentGL2 u y = 0)).mpr hCT
    refine h.mono fun x hx => ?_
    simp only [constantTerm, constantTermIntegrand] at hx
    simpa only [ht, mul_assoc] using hx

  show ∫ a, constantTermIntegrand unipotentGL2 (convOp K f u) g a ∂ν = 0
  simp only [constantTermIntegrand, convOp_apply, rightConv_apply]
  show ∫ a, ∫ x, u (unipotentGL2 a * g * x) * f x ∂μ ∂ν = 0

  have hqmp : Measure.QuasiMeasurePreserving (fun p : AdeleRing (𝓞 K) K × AdelicGL2 (𝓞 K) K => t p.1 * p.2)
      (ν.prod μ) μ := by
    have hsk : MeasurePreserving (fun p : AdeleRing (𝓞 K) K × AdelicGL2 (𝓞 K) K => (p.1, t p.1 * p.2))
        (ν.prod μ) (ν.prod μ) :=
      (MeasurePreserving.id ν).skew_product (g := fun a x => t a * x)
        ((htc.comp continuous_fst).mul continuous_snd).measurable
        (Filter.Eventually.of_forall fun a => map_mul_left_eq_self μ (t a))
    exact Measure.quasiMeasurePreserving_snd.comp hsk.quasiMeasurePreserving
  have hHm : AEStronglyMeasurable (fun p : AdeleRing (𝓞 K) K × AdelicGL2 (𝓞 K) K => u (t p.1 * p.2) * f p.2) (ν.prod μ) :=
    (hmeas.comp_quasiMeasurePreserving hqmp).mul (_hf.comp continuous_snd).aestronglyMeasurable

  obtain ⟨M, hM⟩ := _hf.norm.bddAbove_range_of_hasCompactSupport _hfc.norm
  have hM' : ∀ x, ‖f x‖ ≤ M := fun x => hM ⟨x, rfl⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM' 1)
  obtain ⟨A, hAc, hBA⟩ := exists_isCompact_adelicBox_subset K
  set S := tsupport f with hS
  have hSc : IsCompact S := _hfc
  set C : Set (AdelicGL2 (𝓞 K) K) := (fun p : AdeleRing (𝓞 K) K × AdelicGL2 (𝓞 K) K => t p.1 * p.2) '' (A ×ˢ S) with hC
  have hCc : IsCompact C := (hAc.prod hSc).image ((htc.comp continuous_fst).mul continuous_snd)
  have hIu : ∫⁻ y in C, ‖u y‖ₑ ∂μ < ⊤ := by
    haveI : IsFiniteMeasure (μ.restrict C) := isFiniteMeasure_restrict.2 hCc.measure_lt_top.ne
    have hmem := AutomorphicForm.memLp_two_restrict_of_isCompact_of_isAutomorphicFnAt_canonicalTruncationDomain
      K α β hα hαβ ξK hξc u _hu C hCc
    exact (hmem.integrable one_le_two).2

  have hfib : ∀ a ∈ adelicBox K, ∫⁻ x, ‖u (t a * x) * f x‖ₑ ∂μ ≤ ENNReal.ofReal M * ∫⁻ y in C, ‖u y‖ₑ ∂μ := by
    intro a ha
    have h1 : ∫⁻ x, ‖u (t a * x) * f x‖ₑ ∂μ = ∫⁻ y, ‖u y * f ((t a)⁻¹ * y)‖ₑ ∂μ := by
      rw [← lintegral_mul_left_eq_self (fun y => ‖u y * f ((t a)⁻¹ * y)‖ₑ) (t a)]
      refine lintegral_congr fun x => ?_
      rw [← mul_assoc, inv_mul_cancel, one_mul]
    rw [h1, ← lintegral_indicator hCc.isClosed.measurableSet, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun y => ?_
    rw [enorm_mul]
    by_cases hy : f ((t a)⁻¹ * y) = 0
    · rw [hy, enorm_zero, mul_zero]; exact bot_le
    · have hyC : y ∈ C := by
        refine ⟨(a, (t a)⁻¹ * y), ⟨hBA ha, subset_tsupport _ hy⟩, ?_⟩
        show t a * ((t a)⁻¹ * y) = y
        rw [← mul_assoc, mul_inv_cancel, one_mul]
      rw [Set.indicator_of_mem hyC, mul_comm]
      refine mul_le_mul_left ?_ _
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hM' _)
  have hint : Integrable (Function.uncurry fun (a : AdeleRing (𝓞 K) K) (x : AdelicGL2 (𝓞 K) K) => u (t a * x) * f x)
      (ν.prod μ) := by
    refine ⟨hHm, ?_⟩
    show ∫⁻ p, ‖u (t p.1 * p.2) * f p.2‖ₑ ∂(ν.prod μ) < ⊤
    rw [lintegral_prod _ hHm.enorm]
    have hνB : ∀ᵐ a ∂ν, a ∈ adelicBox K := by
      have h0 : ν (adelicBox K)ᶜ = 0 := by
        rw [hνdef, ProbabilityTheory.cond, Measure.smul_apply, Measure.restrict_apply (measurableSet_adelicBox K).compl,
          Set.compl_inter_self, measure_empty, smul_zero]
      have h1 : ∀ᵐ a ∂ν, a ∉ (adelicBox K)ᶜ := measure_eq_zero_iff_ae_notMem.mp h0
      exact h1.mono fun a ha => by simpa using ha
    calc ∫⁻ a, ∫⁻ x, ‖u (t a * x) * f x‖ₑ ∂μ ∂ν
        ≤ ∫⁻ a, ENNReal.ofReal M * ∫⁻ y in C, ‖u y‖ₑ ∂μ ∂ν := lintegral_mono_ae (hνB.mono fun a ha => hfib a ha)
      _ = ENNReal.ofReal M * (∫⁻ y in C, ‖u y‖ₑ ∂μ) * ν Set.univ := by rw [lintegral_const]
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hIu) (measure_lt_top ν _)

  have hswap := integral_integral_swap hint
  simp only [ht] at hswap
  rw [show (∫ a, ∫ x, u (unipotentGL2 a * g * x) * f x ∂μ ∂ν) = ∫ x, ∫ a, u (unipotentGL2 a * g * x) * f x ∂ν ∂μ from hswap]
  have hinner : ∀ᵐ x ∂μ, (∫ a, u (unipotentGL2 a * g * x) * f x ∂ν) = 0 := by
    refine hae.mono fun x hx => ?_
    rw [integral_mul_const]
    simp only [ht] at hx
    rw [hx, zero_mul]
  rw [integral_congr_ae hinner, integral_zero]

end S_AutomorphicForm_constantTerm_convOp_eq_zero_of_ae_constantTerm_eq_zero_of_isAutomorphicFnAt
end P2MW
export P2MW.S_AutomorphicForm_constantTerm_convOp_eq_zero_of_ae_constantTerm_eq_zero_of_isAutomorphicFnAt (solution)
