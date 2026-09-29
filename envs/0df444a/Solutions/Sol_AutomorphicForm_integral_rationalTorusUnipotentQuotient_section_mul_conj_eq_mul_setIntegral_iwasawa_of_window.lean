-- Prove2me | solution 1 for AutomorphicForm.integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa_of_window
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/ddd8fec4-791e-5aea-9cee-8b86b9cdf10c

import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Theorems.Thm_NumberField_Idele_exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const
import Theorems.Thm_NumberField_Idele_exists_setLIntegral_comp_ideleNorm_eq_mul_lintegral_Ioi
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa_of_window
p2m_attr_erase "instance" "FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal
open scoped NNReal ENNReal Topology

noncomputable section

namespace KcWindow

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

section Prelim

variable (F : Type) [Field F] [NumberField F]

theorem secondCountableTopology_idele : SecondCountableTopology (AdeleRing (𝓞 F) F)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem sigmaFinite_idelicHaar : SigmaFinite (NumberField.Idele.idelicHaar F) := by
  haveI := secondCountableTopology_idele F
  infer_instance

theorem continuous_det :
    Continuous fun g : AdelicGL2 (𝓞 F) F => Matrix.GeneralLinearGroup.det g := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_det
  · exact Units.continuous_coe_inv.matrix_det

theorem continuous_diagOne :
    Continuous (diagOne : (AdeleRing (𝓞 F) F)ˣ → AdelicGL2 (𝓞 F) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => Matrix.diagonal ![(t : AdeleRing (𝓞 F) F), 1]
    exact (Units.continuous_val.matrixVecCons continuous_const).matrix_diagonal
  · show Continuous fun t : (AdeleRing (𝓞 F) F)ˣ =>
      Matrix.diagonal ![((t⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 1]
    exact (Units.continuous_coe_inv.matrixVecCons continuous_const).matrix_diagonal

theorem continuous_centralScalar :
    Continuous (centralScalar (𝓞 F) F : (AdeleRing (𝓞 F) F)ˣ → AdelicGL2 (𝓞 F) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun u : (AdeleRing (𝓞 F) F)ˣ => Matrix.diagonal fun _ : Fin 2 => (u : AdeleRing (𝓞 F) F)
    exact (continuous_pi fun _ => Units.continuous_val).matrix_diagonal
  · show Continuous fun u : (AdeleRing (𝓞 F) F)ˣ =>
      Matrix.diagonal fun _ : Fin 2 => ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
    exact (continuous_pi fun _ => Units.continuous_coe_inv).matrix_diagonal

theorem continuous_word3 :
    Continuous fun p : ((AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ) × adelicMaximalCompact F =>
      centralScalar (𝓞 F) F p.1.1 * diagOne p.1.2 * (p.2 : AdelicGL2 (𝓞 F) F) :=
  (((continuous_centralScalar F).comp continuous_fst.fst).mul
    ((continuous_diagOne F).comp continuous_fst.snd)).mul (continuous_subtype_val.comp continuous_snd)

theorem measurable_word3 :
    Measurable fun p : ((AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ) × adelicMaximalCompact F =>
      centralScalar (𝓞 F) F p.1.1 * diagOne p.1.2 * (p.2 : AdelicGL2 (𝓞 F) F) := by
  haveI := secondCountableTopology_idele F
  exact (continuous_word3 F).measurable

theorem measurable_wt :
    Measurable fun p : ((AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ) × adelicMaximalCompact F =>
      ENNReal.ofReal ((ideleNorm F p.1.2)⁻¹) :=
  ENNReal.measurable_ofReal.comp
    (((NumberField.TateGlobal.continuous_ideleNorm F).measurable.comp measurable_fst.snd).inv)

end Prelim

section Abstract

variable (F : Type) [Field F] [NumberField F]

theorem measurable_mk :
    Measurable (Quotient.mk'' : AdelicGL2 (𝓞 F) F → RationalTorusUnipotentQuotient F) :=
  measurable_quotient_mk''

theorem apply_out_mk {β : Type*} (Fc : AdelicGL2 (𝓞 F) F → β)
    (hFinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, Fc (x * g) = Fc g)
    (g : AdelicGL2 (𝓞 F) F) :
    Fc ((Quotient.mk'' g : RationalTorusUnipotentQuotient F).out) = Fc g := by
  have h : (Quotient.mk'' ((Quotient.mk'' g : RationalTorusUnipotentQuotient F).out) :
      RationalTorusUnipotentQuotient F) = Quotient.mk'' g := Quotient.out_eq' _
  rw [Quotient.eq''] at h
  obtain ⟨x, hx⟩ := MulAction.orbitRel_apply.mp h
  have hx' : (x : AdelicGL2 (𝓞 F) F) * g = (Quotient.mk'' g : RationalTorusUnipotentQuotient F).out := hx
  rw [← hx', hFinv _ x.2]

theorem integrable_and_integral_eq_of_lintegral
    (c : ℝ≥0∞) (hc_top : c ≠ ∞)
    (hc : ∀ (D D' : Set (AdeleRing (𝓞 F) F)ˣ), MeasurableSet D → MeasurableSet D' →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F) →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F) →
      ∀ f : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable f →
        (∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (x * g) = f g) →
        ∫⁻ q, f q.out ∂(rationalTorusUnipotentQuotientMeasure F) =
          c * ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
                f (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
                  ENNReal.ofReal ((ideleNorm F t)⁻¹)
              ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F))
    (D D' : Set (AdeleRing (𝓞 F) F)ˣ) (hD : MeasurableSet D) (hD' : MeasurableSet D')
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (hD'F : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F))
    (Fc : AdelicGL2 (𝓞 F) F → ℂ) (hFm : Measurable Fc)
    (hFinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, Fc (x * g) = Fc g)
    (hfin : ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
        ‖Fc (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F))‖ₑ *
          ENNReal.ofReal ((ideleNorm F t)⁻¹)
        ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) < ⊤) :
    Integrable (fun q : RationalTorusUnipotentQuotient F => Fc q.out) (rationalTorusUnipotentQuotientMeasure F) ∧
    ∫ q : RationalTorusUnipotentQuotient F, Fc q.out ∂(rationalTorusUnipotentQuotientMeasure F) =
      (c.toReal : ℂ) * ∫ z in D, ∫ t in D', ∫ k,
          Fc (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) * (((ideleNorm F t)⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) := by
  haveI := secondCountableTopology_idele F
  haveI := sigmaFinite_idelicHaar F

  set ν := NumberField.Idele.idelicHaar F with hν
  set mK := maximalCompactHaar F with hmK
  set νT := rationalTorusUnipotentQuotientMeasure F with hνT
  set ψ : ((AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ) × adelicMaximalCompact F →
      RationalTorusUnipotentQuotient F := fun p =>
    Quotient.mk'' (centralScalar (𝓞 F) F p.1.1 * diagOne p.1.2 * (p.2 : AdelicGL2 (𝓞 F) F)) with hψ
  set wt : ((AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ) × adelicMaximalCompact F → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((ideleNorm F p.1.2)⁻¹) with hwt
  set ρ : Measure (((AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ) × adelicMaximalCompact F) :=
    ((ν.restrict D).prod (ν.restrict D')).prod mK with hρ
  have hψm : Measurable ψ := (measurable_mk F).comp (measurable_word3 F)
  have hwtm : Measurable wt := measurable_wt F
  have hwt_top : ∀ p, wt p < ⊤ := fun p => ENNReal.ofReal_lt_top

  have hout : ∀ g : AdelicGL2 (𝓞 F) F,
      Fc ((Quotient.mk'' g : RationalTorusUnipotentQuotient F).out) = Fc g := apply_out_mk F Fc hFinv

  have hM : νT = c • (ρ.withDensity wt).map ψ := by
    ext E hE
    have hpre : MeasurableSet ((Quotient.mk'' : AdelicGL2 (𝓞 F) F → RationalTorusUnipotentQuotient F) ⁻¹' E) :=
      measurable_mk F hE
    have h1 : νT E = ∫⁻ q, ((Quotient.mk'' : AdelicGL2 (𝓞 F) F → RationalTorusUnipotentQuotient F) ⁻¹' E).indicator
        (fun _ => (1 : ℝ≥0∞)) q.out ∂νT := by
      rw [← lintegral_indicator_one hE]
      refine lintegral_congr fun q => ?_
      have hq : (q.out ∈ (Quotient.mk'' : AdelicGL2 (𝓞 F) F → RationalTorusUnipotentQuotient F) ⁻¹' E) ↔
          q ∈ E := by
        rw [Set.mem_preimage, Quotient.out_eq']
      by_cases h : q ∈ E
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hq.mpr h), Pi.one_apply]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hq.mp h'))]
    have hinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F,
        ((Quotient.mk'' : AdelicGL2 (𝓞 F) F → RationalTorusUnipotentQuotient F) ⁻¹' E).indicator
          (fun _ => (1 : ℝ≥0∞)) (x * g) =
        ((Quotient.mk'' : AdelicGL2 (𝓞 F) F → RationalTorusUnipotentQuotient F) ⁻¹' E).indicator
          (fun _ => (1 : ℝ≥0∞)) g := by
      intro x hx g
      have hq : (Quotient.mk'' (x * g) : RationalTorusUnipotentQuotient F) = Quotient.mk'' g := by
        rw [Quotient.eq'']
        exact MulAction.orbitRel_apply.mpr ⟨⟨x, hx⟩, rfl⟩
      have hmem : (x * g ∈ (Quotient.mk'' : AdelicGL2 (𝓞 F) F → RationalTorusUnipotentQuotient F) ⁻¹' E) ↔
          g ∈ (Quotient.mk'' : AdelicGL2 (𝓞 F) F → RationalTorusUnipotentQuotient F) ⁻¹' E := by
        rw [Set.mem_preimage, Set.mem_preimage, hq]
      by_cases h : g ∈ (Quotient.mk'' : AdelicGL2 (𝓞 F) F → RationalTorusUnipotentQuotient F) ⁻¹' E
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.mpr h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hmem.mp h'))]
    rw [h1, hc D D' hD hD' hDF hD'F _ (measurable_const.indicator hpre) hinv, Measure.smul_apply, smul_eq_mul,
      Measure.map_apply hψm hE, withDensity_apply _ (hψm hE), ← lintegral_indicator (hψm hE), hρ,
      lintegral_prod _ ((hwtm.indicator (hψm hE)).aemeasurable),
      lintegral_prod _ ((hwtm.indicator (hψm hE)).lintegral_prod_right'
        (ν := mK)).aemeasurable]
    congr 1
    refine lintegral_congr fun z => lintegral_congr fun t => lintegral_congr fun k => ?_
    by_cases h : (Quotient.mk'' (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) :
        RationalTorusUnipotentQuotient F) ∈ E
    · have h1 : centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F) ∈
          (Quotient.mk'' : AdelicGL2 (𝓞 F) F → RationalTorusUnipotentQuotient F) ⁻¹' E := h
      have h2 : ((z, t), k) ∈ ψ ⁻¹' E := h
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, one_mul]
    · have h1 : centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F) ∉
          (Quotient.mk'' : AdelicGL2 (𝓞 F) F → RationalTorusUnipotentQuotient F) ⁻¹' E := h
      have h2 : ((z, t), k) ∉ ψ ⁻¹' E := h
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, zero_mul]

  have hcomp : (fun q : RationalTorusUnipotentQuotient F => Fc q.out) ∘ ψ =
      fun p => Fc (centralScalar (𝓞 F) F p.1.1 * diagOne p.1.2 * (p.2 : AdelicGL2 (𝓞 F) F)) := by
    funext p
    exact hout _
  have hFqm : Measurable fun q : RationalTorusUnipotentQuotient F => Fc q.out := by
    rw [measurable_from_quotient]
    have : (fun q : RationalTorusUnipotentQuotient F => Fc q.out) ∘ Quotient.mk'' = Fc := funext fun g => hout g
    rw [this]
    exact hFm
  have hGm : Measurable fun p : ((AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ) × adelicMaximalCompact F =>
      Fc (centralScalar (𝓞 F) F p.1.1 * diagOne p.1.2 * (p.2 : AdelicGL2 (𝓞 F) F)) :=
    hFm.comp (measurable_word3 F)

  have hint : Integrable (fun p : ((AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ) × adelicMaximalCompact F =>
      (wt p).toReal • Fc (centralScalar (𝓞 F) F p.1.1 * diagOne p.1.2 * (p.2 : AdelicGL2 (𝓞 F) F))) ρ := by
    refine ⟨(hwtm.ennreal_toReal.smul hGm).aestronglyMeasurable, ?_⟩
    show (∫⁻ p, ‖(wt p).toReal • Fc (centralScalar (𝓞 F) F p.1.1 * diagOne p.1.2 *
      (p.2 : AdelicGL2 (𝓞 F) F))‖ₑ ∂ρ) < ⊤
    have heq : ∀ p : ((AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ) × adelicMaximalCompact F,
        ‖(wt p).toReal • Fc (centralScalar (𝓞 F) F p.1.1 * diagOne p.1.2 * (p.2 : AdelicGL2 (𝓞 F) F))‖ₑ =
        ‖Fc (centralScalar (𝓞 F) F p.1.1 * diagOne p.1.2 * (p.2 : AdelicGL2 (𝓞 F) F))‖ₑ * wt p := by
      intro p
      rw [enorm_smul, mul_comm]
      congr 1
      rw [hwt]
      simp only
      rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ENNReal.ofReal_ne_top]
    simp_rw [heq]
    rw [hρ, lintegral_prod _ ((hGm.enorm.fun_mul hwtm).aemeasurable),
      lintegral_prod _ ((hGm.enorm.fun_mul hwtm).lintegral_prod_right' (ν := mK)).aemeasurable]
    exact hfin
  have hint' : Integrable ((fun q : RationalTorusUnipotentQuotient F => Fc q.out) ∘ ψ) (ρ.withDensity wt) := by
    rw [integrable_withDensity_iff_integrable_smul' hwtm (ae_of_all _ hwt_top), hcomp]
    exact hint
  have hintegrable : Integrable (fun q : RationalTorusUnipotentQuotient F => Fc q.out) νT := by
    rw [hM]
    refine Integrable.smul_measure ?_ hc_top
    exact (integrable_map_measure hFqm.aestronglyMeasurable hψm.aemeasurable).mpr hint'
  refine ⟨hintegrable, ?_⟩

  rw [hM, integral_smul_measure, integral_map hψm.aemeasurable hFqm.aestronglyMeasurable]
  change c.toReal • ∫ p, ((fun q : RationalTorusUnipotentQuotient F => Fc q.out) ∘ ψ) p ∂(ρ.withDensity wt) = _
  rw [integral_withDensity_eq_integral_toReal_smul hwtm (ae_of_all _ hwt_top), hcomp]
  simp only []
  rw [hρ, integral_prod _ hint, integral_prod _ hint.integral_prod_left, Complex.real_smul]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun z => integral_congr_ae (ae_of_all _ fun t =>
    integral_congr_ae (ae_of_all _ fun k => ?_)))
  simp only [hwt]
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (ideleNorm_pos t).le), Complex.real_smul, mul_comm]

end Abstract

section Integrand

variable (F : Type) [Field F] [NumberField F]

theorem det_diagOne {A : Type*} [CommRing A] (t : Aˣ) :
    Matrix.GeneralLinearGroup.det (diagOne t : GL (Fin 2) A) = t := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show (Matrix.diagonal ![(t : A), 1]).det = t
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  simp

theorem ideleNorm_map_algebraMap (u : Fˣ) :
    ideleNorm F (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u) = 1 := by
  have h := AutomorphicForm.ideleNorm_det_globalPoints (F := F) (diagOne u)
  have hdet : Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F (diagOne u)) =
      Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u := by
    show Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.map (algebraMap F (AdeleRing (𝓞 F) F)) (diagOne u)) = _
    rw [Matrix.GeneralLinearGroup.map_det, det_diagOne]
  rwa [hdet] at h

theorem ideleNorm_one : ideleNorm F 1 = 1 := by
  simp [ideleNorm]

theorem isPrincipalTrivial_of_eq (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hαN : ∀ x, ((α x : ℝˣ) : ℝ) = ideleNorm F x) : IsPrincipalTrivial (R := 𝓞 F) (K := F) α := by
  intro u
  refine Units.ext ?_
  rw [hαN, Units.val_one]
  exact ideleNorm_map_algebraMap F u

theorem diagOne_mem_adelicBorel (t : (AdeleRing (𝓞 F) F)ˣ) : (diagOne t : AdelicGL2 (𝓞 F) F) ∈ adelicBorel (𝓞 F) F := by
  show (Matrix.diagonal ![(t : AdeleRing (𝓞 F) F), 1]) 1 0 = 0
  exact Matrix.diagonal_apply_ne _ (by decide)

theorem centralScalar_mul_diagOne_mem (z t : (AdeleRing (𝓞 F) F)ˣ) :
    centralScalar (𝓞 F) F z * diagOne t ∈ adelicBorel (𝓞 F) F :=
  Subgroup.mul_mem _ (centralScalar_mem_adelicBorel (𝓞 F) F z) (diagOne_mem_adelicBorel F t)

theorem coe_centralScalar_mul_diagOne (z t : (AdeleRing (𝓞 F) F)ˣ) :
    ((centralScalar (𝓞 F) F z * diagOne t : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
      Matrix.diagonal fun i => (z : AdeleRing (𝓞 F) F) * ![(t : AdeleRing (𝓞 F) F), 1] i := by
  rw [Units.val_mul]
  show Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F) * Matrix.diagonal ![(t : AdeleRing (𝓞 F) F), 1] = _
  rw [Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]

theorem borelDiagFst_centralScalar_mul_diagOne (z t : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagFst (⟨centralScalar (𝓞 F) F z * diagOne t, centralScalar_mul_diagOne_mem F z t⟩ :
      ↥(adelicBorel (𝓞 F) F)) = z * t := by
  refine Units.ext ?_
  show ((centralScalar (𝓞 F) F z * diagOne t : AdelicGL2 (𝓞 F) F) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = z * t
  rw [coe_centralScalar_mul_diagOne, Matrix.diagonal_apply_eq]
  rfl

theorem borelDiagSnd_centralScalar_mul_diagOne (z t : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagSnd (⟨centralScalar (𝓞 F) F z * diagOne t, centralScalar_mul_diagOne_mem F z t⟩ :
      ↥(adelicBorel (𝓞 F) F)) = z := by
  refine Units.ext ?_
  show ((centralScalar (𝓞 F) F z * diagOne t : AdelicGL2 (𝓞 F) F) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = z
  rw [coe_centralScalar_mul_diagOne, Matrix.diagonal_apply_eq]
  show (z : AdeleRing (𝓞 F) F) * 1 = z
  rw [mul_one]

theorem section_word {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ) (z t : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    φ (centralScalar (𝓞 F) F z * diagOne t * g) = ((χ₁ (z * t) : ℂˣ) : ℂ) * ((χ₂ z : ℂˣ) : ℂ) * φ g := by
  rw [hφ _ (centralScalar_mul_diagOne_mem F z t) g, borelDiagFst_centralScalar_mul_diagOne,
    borelDiagSnd_centralScalar_mul_diagOne]

theorem adelicHeight_borel_mul {b : AdelicGL2 (𝓞 F) F} (hb : b ∈ adelicBorel (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    NumberField.AdelicHeight.adelicHeight F (b * g) =
      ideleNorm F (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) *
        (ideleNorm F (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))))⁻¹ *
          NumberField.AdelicHeight.adelicHeight F g := by
  obtain ⟨hpos, -, hsec⟩ := AutomorphicForm.isInducedSection_adelicHeight_cpow F
  have h := hsec hpos (1 / 2) b hb g
  have hhalf : (1 / 2 : ℂ) + 1 / 2 = 1 := by norm_num
  simp only [hhalf, Complex.cpow_one, etaFst_apply, etaSnd_apply, cpowChar_apply_val,
    Complex.cpow_neg_one, MonoidHom.one_apply, one_mul] at h
  have e1 : ∀ x : (AdeleRing (𝓞 F) F)ˣ,
      ((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits x :
        ℝˣ) : ℝ) = ideleNorm F x := fun x => rfl
  rw [e1, e1] at h
  have hg0 : ((ideleNorm F (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ideleNorm_pos _).ne'
  apply Complex.ofReal_injective
  rw [h]
  push_cast
  ring

theorem adelicHeight_maximalCompact (k : adelicMaximalCompact F) :
    NumberField.AdelicHeight.adelicHeight F (k : AdelicGL2 (𝓞 F) F) = 1 := by
  rw [NumberField.AdelicHeight.adelicHeight_eq_archHeight_of_mem k.2.1]
  have h := AutomorphicForm.WindowedSiegel.archHeight_mul_rowIsometry F 1
    (k := glArch (𝓞 F) F (k : AdelicGL2 (𝓞 F) F)) k.2.2
  rwa [one_mul, AutomorphicForm.WindowedSiegel.archHeight_one] at h

theorem adelicHeight_word (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F) :
    NumberField.AdelicHeight.adelicHeight F (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) =
      ideleNorm F t := by
  rw [adelicHeight_borel_mul F (centralScalar_mul_diagOne_mem F z t), borelDiagFst_centralScalar_mul_diagOne,
    borelDiagSnd_centralScalar_mul_diagOne, adelicHeight_maximalCompact, ideleNorm_mul, mul_one]
  have hz : ideleNorm F z ≠ 0 := (ideleNorm_pos z).ne'
  field_simp

theorem adelicHeight_unipotentGL2_mul (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    NumberField.AdelicHeight.adelicHeight F (unipotentGL2 x * g) = NumberField.AdelicHeight.adelicHeight F g := by
  rw [adelicHeight_borel_mul F (unipotentGL2_mem_borelSubgroup x), borelDiagFst_unipotentGL2,
    borelDiagSnd_unipotentGL2, ideleNorm_one, inv_one, one_mul, one_mul]

theorem adelicHeight_globalPoints_mul {γ : GL (Fin 2) F} (hγ : γ ∈ borelSubgroup F) (g : AdelicGL2 (𝓞 F) F) :
    NumberField.AdelicHeight.adelicHeight F (globalPoints (𝓞 F) F γ * g) =
      NumberField.AdelicHeight.adelicHeight F g := by
  rw [adelicHeight_borel_mul F (globalPoints_mem_adelicBorel (𝓞 F) F hγ),
    borelDiagFst_globalPoints (𝓞 F) F hγ, borelDiagSnd_globalPoints (𝓞 F) F hγ, ideleNorm_map_algebraMap,
    ideleNorm_map_algebraMap, inv_one, one_mul, one_mul]

theorem det_unipotentGL2 (x : AdeleRing (𝓞 F) F) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x : AdelicGL2 (𝓞 F) F) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, AutomorphicForm.unipotentGL2_coe, Matrix.det_fin_two_of]
  simp only [mul_one, mul_zero, sub_zero, Units.val_one]

theorem det_centralScalar (u : (AdeleRing (𝓞 F) F)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F u) = u * u := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show (Matrix.scalar (Fin 2) (u : AdeleRing (𝓞 F) F)).det = u * u
  rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two]

theorem ideleNorm_det_maximalCompact (k : adelicMaximalCompact F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 F) F)) = 1 := by
  set f : adelicMaximalCompact F → ℝ := fun k =>
    ideleNorm F (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 F) F)) with hf
  have hfc : Continuous f :=
    (NumberField.TateGlobal.continuous_ideleNorm F).comp ((continuous_det F).comp continuous_subtype_val)
  have hmul : ∀ k k' : adelicMaximalCompact F, f (k * k') = f k * f k' := by
    intro k k'
    simp only [hf, Subgroup.coe_mul, map_mul, ideleNorm_mul]
  have hone : f 1 = 1 := by
    simp only [hf, OneMemClass.coe_one, map_one]
    exact ideleNorm_one F
  have hpow : ∀ (k : adelicMaximalCompact F) (n : ℕ), f (k ^ n) = f k ^ n := by
    intro k n
    induction n with
    | zero => rw [pow_zero, pow_zero, hone]
    | succ n ih => rw [pow_succ, pow_succ, hmul, ih]
  have hinv : ∀ k : adelicMaximalCompact F, f k⁻¹ = (f k)⁻¹ := by
    intro k
    have h1 : f (k⁻¹ * k) = f k⁻¹ * f k := hmul _ _
    rw [inv_mul_cancel, hone] at h1
    have hpos : 0 < f k := ideleNorm_pos _
    field_simp
    linarith [h1]
  obtain ⟨M, hM⟩ := (isCompact_range hfc).bddAbove
  have hbound : ∀ k : adelicMaximalCompact F, f k ≤ M := fun k => hM ⟨k, rfl⟩
  have hle : ∀ k : adelicMaximalCompact F, f k ≤ 1 := by
    intro k
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hlt
    exact (lt_irrefl M) (hn.trans_le (by rw [← hpow]; exact hbound _))
  have hge : 1 ≤ f k := by
    have h := hle k⁻¹
    rw [hinv] at h
    have hpos : 0 < f k := ideleNorm_pos _
    exact (inv_le_one₀ hpos).mp h
  exact le_antisymm (hle k) hge

theorem ideleNorm_det_word (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det
      (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F))) = ideleNorm F z ^ 2 * ideleNorm F t := by
  rw [map_mul, map_mul, det_centralScalar, det_diagOne, ideleNorm_mul, ideleNorm_mul, ideleNorm_mul,
    ideleNorm_det_maximalCompact, mul_one, sq]

def integrand (a b : ℝ) (I : Set ℝ) (φ φ' : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}.indicator
      (fun _ => (1 : ℂ)) g *
    I.indicator (fun _ => (1 : ℂ)) (NumberField.AdelicHeight.adelicHeight F g) * (φ g * (starRingEnd ℂ) (φ' g))

theorem measurableSet_detShell (a b : ℝ) :
    MeasurableSet {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b} :=
  ((NumberField.TateGlobal.continuous_ideleNorm F).comp (continuous_det F)).measurable measurableSet_Icc

theorem measurable_integrand (a b : ℝ) {I : Set ℝ} (hI : MeasurableSet I) {φ φ' : AdelicGL2 (𝓞 F) F → ℂ}
    (hφc : Continuous φ) (hφ'c : Continuous φ') : Measurable (integrand F a b I φ φ') :=
  ((measurable_const.indicator (measurableSet_detShell F a b)).mul
    ((measurable_const.indicator hI).comp (NumberField.AdelicHeight.continuous_adelicHeight F).measurable)).mul
    (hφc.measurable.mul (Complex.continuous_conj.measurable.comp hφ'c.measurable))

def stab {β : Type*} (f : AdelicGL2 (𝓞 F) F → β) : Subgroup (AdelicGL2 (𝓞 F) F) where
  carrier := {x | ∀ g, f (x * g) = f g}
  one_mem' := fun g => by rw [one_mul]
  mul_mem' := fun {x y} hx hy g => by
    show f (x * y * g) = f g
    rw [mul_assoc, hx, hy]
  inv_mem' := fun {x} hx g => by
    show f (x⁻¹ * g) = f g
    rw [← hx (x⁻¹ * g), mul_inv_cancel_left]

theorem integrand_globalPoints_mul (a b : ℝ) (I : Set ℝ)
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαN : ∀ x, ((α x : ℝˣ) : ℝ) = ideleNorm F x)
    (μ ν μ' ν' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμF : IsIdeleClassChar (𝓞 F) F μ) (hνF : IsIdeleClassChar (𝓞 F) F ν)
    (hμ'F : IsIdeleClassChar (𝓞 F) F μ') (hν'F : IsIdeleClassChar (𝓞 F) F ν')
    (s s' : ℂ) {φ φ' : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
    (hφ' : IsInducedSection (𝓞 F) F (etaFst μ' α hα s') (etaSnd ν' α hα s') φ')
    {γ : GL (Fin 2) F} (hγ : γ ∈ borelSubgroup F) (g : AdelicGL2 (𝓞 F) F) :
    integrand F a b I φ φ' (globalPoints (𝓞 F) F γ * g) = integrand F a b I φ φ' g := by
  have hprin := isPrincipalTrivial_of_eq F α hαN
  have hmem := globalPoints_mem_adelicBorel (𝓞 F) F hγ
  have hφe : φ (globalPoints (𝓞 F) F γ * g) = φ g := by
    rw [hφ _ hmem g, borelDiagFst_globalPoints (𝓞 F) F hγ, borelDiagSnd_globalPoints (𝓞 F) F hγ,
      etaFst_isIdeleClassChar hμF hprin, etaSnd_isIdeleClassChar hνF hprin, Units.val_one, one_mul, one_mul]
  have hφ'e : φ' (globalPoints (𝓞 F) F γ * g) = φ' g := by
    rw [hφ' _ hmem g, borelDiagFst_globalPoints (𝓞 F) F hγ, borelDiagSnd_globalPoints (𝓞 F) F hγ,
      etaFst_isIdeleClassChar hμ'F hprin, etaSnd_isIdeleClassChar hν'F hprin, Units.val_one, one_mul, one_mul]
  have hdet : ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F γ * g)) =
      ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
    rw [map_mul, ideleNorm_mul, AutomorphicForm.ideleNorm_det_globalPoints, one_mul]
  unfold integrand
  rw [hφe, hφ'e, adelicHeight_globalPoints_mul F hγ]
  simp only [Set.indicator_apply, Set.mem_setOf_eq, hdet]

theorem integrand_unipotentGL2_mul (a b : ℝ) (I : Set ℝ)
    {χ₁ χ₂ χ₁' χ₂' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {φ φ' : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ) (hφ' : IsInducedSection (𝓞 F) F χ₁' χ₂' φ')
    (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    integrand F a b I φ φ' (unipotentGL2 x * g) = integrand F a b I φ φ' g := by
  have hdet : ideleNorm F (Matrix.GeneralLinearGroup.det (unipotentGL2 x * g)) =
      ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
    rw [map_mul, det_unipotentGL2, one_mul]
  unfold integrand
  rw [isInducedSection_unipotent_mul hφ, isInducedSection_unipotent_mul hφ', adelicHeight_unipotentGL2_mul]
  simp only [Set.indicator_apply, Set.mem_setOf_eq, hdet]

theorem integrand_mul_of_mem (a b : ℝ) (I : Set ℝ)
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαN : ∀ x, ((α x : ℝˣ) : ℝ) = ideleNorm F x)
    (μ ν μ' ν' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμF : IsIdeleClassChar (𝓞 F) F μ) (hνF : IsIdeleClassChar (𝓞 F) F ν)
    (hμ'F : IsIdeleClassChar (𝓞 F) F μ') (hν'F : IsIdeleClassChar (𝓞 F) F ν')
    (s s' : ℂ) {φ φ' : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
    (hφ' : IsInducedSection (𝓞 F) F (etaFst μ' α hα s') (etaSnd ν' α hα s') φ') :
    ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F,
      integrand F a b I φ φ' (x * g) = integrand F a b I φ φ' g := by
  suffices h : rationalTorusUnipotent F ≤ stab F (integrand F a b I φ φ') from fun x hx g => h hx g
  refine sup_le (sup_le ?_ ?_) ?_
  · rintro _ ⟨u, rfl⟩ g
    refine integrand_globalPoints_mul F a b I α hα hαN μ ν μ' ν' hμF hνF hμ'F hν'F s s' hφ hφ' ?_ g
    show ((Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom u : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 1 0 = 0
    show (Matrix.scalar (Fin 2) (u : F)) 1 0 = 0
    rw [Matrix.scalar_apply]
    exact Matrix.diagonal_apply_ne _ (by decide)
  · rintro _ ⟨u, rfl⟩ g
    refine integrand_globalPoints_mul F a b I α hα hαN μ ν μ' ν' hμF hνF hμ'F hν'F s s' hφ hφ' ?_ g
    show (Matrix.diagonal ![(u : F), 1]) 1 0 = 0
    exact Matrix.diagonal_apply_ne _ (by decide)
  · rintro _ ⟨m, rfl⟩ g
    exact integrand_unipotentGL2_mul F a b I hφ hφ' _ g

theorem integrand_word (a b : ℝ) (I : Set ℝ)
    {χ₁ χ₂ χ₁' χ₂' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {φ φ' : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ) (hφ' : IsInducedSection (𝓞 F) F χ₁' χ₂' φ')
    (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F) :
    integrand F a b I φ φ' (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) =
      (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t) *
        I.indicator (fun _ => (1 : ℂ)) (ideleNorm F t) *
        ((((χ₁ (z * t) : ℂˣ) : ℂ) * ((χ₂ z : ℂˣ) : ℂ) * φ (k : AdelicGL2 (𝓞 F) F)) *
          (starRingEnd ℂ) (((χ₁' (z * t) : ℂˣ) : ℂ) * ((χ₂' z : ℂˣ) : ℂ) * φ' (k : AdelicGL2 (𝓞 F) F))) := by
  unfold integrand
  rw [section_word F hφ, section_word F hφ', adelicHeight_word]
  simp only [Set.indicator_apply, Set.mem_setOf_eq, ideleNorm_det_word]

theorem norm_etaSnd_apply_of_unitary {ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hν : IsUnitaryChar (𝓞 F) F ν)
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) (x : (AdeleRing (𝓞 F) F)ˣ) :
    ‖((etaSnd ν α hα s x : ℂˣ) : ℂ)‖ = ((α x : ℝˣ) : ℝ) ^ (-(s.re + 1 / 2)) := by
  rw [etaSnd_apply, Units.val_mul, norm_mul, hν x, one_mul, norm_cpowChar_apply]
  congr 1
  rw [Complex.neg_re, re_add_half]

theorem norm_eta_pair (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαN : ∀ x, ((α x : ℝˣ) : ℝ) = ideleNorm F x)
    {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (s : ℂ) (z t : (AdeleRing (𝓞 F) F)ˣ) :
    ‖((etaFst μ α hα s (z * t) : ℂˣ) : ℂ) * ((etaSnd ν α hα s z : ℂˣ) : ℂ)‖ =
      ideleNorm F t ^ (s.re + 1 / 2) := by
  rw [norm_mul, norm_etaFst_apply_of_unitary hμ, norm_etaSnd_apply_of_unitary F hν, hαN, hαN, ideleNorm_mul,
    Real.mul_rpow (ideleNorm_pos z).le (ideleNorm_pos t).le, Real.rpow_neg (ideleNorm_pos z).le]
  have hz : ideleNorm F z ^ (s.re + 1 / 2) ≠ 0 := (Real.rpow_pos_of_pos (ideleNorm_pos z) _).ne'
  rw [mul_right_comm, mul_inv_cancel₀ hz, one_mul]

theorem enorm_integrand_word_mul (a b : ℝ) (I : Set ℝ)
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαN : ∀ x, ((α x : ℝˣ) : ℝ) = ideleNorm F x)
    {μ ν μ' ν' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (hμ' : IsUnitaryChar (𝓞 F) F μ') (hν' : IsUnitaryChar (𝓞 F) F ν')
    (s s' : ℂ) {φ φ' : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
    (hφ' : IsInducedSection (𝓞 F) F (etaFst μ' α hα s') (etaSnd ν' α hα s') φ')
    (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F) :
    ‖integrand F a b I φ φ' (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F))‖ₑ *
        ENNReal.ofReal ((ideleNorm F t)⁻¹) =
      {z' : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F z' ^ 2 * ideleNorm F t ∈ Set.Icc a b}.indicator
          (fun _ => (1 : ℝ≥0∞)) z *
        ENNReal.ofReal (I.indicator (fun _ => (1 : ℝ)) (ideleNorm F t) * ideleNorm F t ^ (s.re + s'.re)) *
        (‖φ (k : AdelicGL2 (𝓞 F) F)‖ₑ * ‖φ' (k : AdelicGL2 (𝓞 F) F)‖ₑ) := by
  rw [integrand_word F a b I hφ hφ']
  have ht0 : 0 < ideleNorm F t := ideleNorm_pos t

  have h1 : ‖(Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t)‖ₑ =
      {z' : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F z' ^ 2 * ideleNorm F t ∈ Set.Icc a b}.indicator
        (fun _ => (1 : ℝ≥0∞)) z := by
    by_cases h : ideleNorm F z ^ 2 * ideleNorm F t ∈ Set.Icc a b
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show z ∈ {z' : (AdeleRing (𝓞 F) F)ˣ |
        ideleNorm F z' ^ 2 * ideleNorm F t ∈ Set.Icc a b} from h), enorm_one]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show z ∉ {z' : (AdeleRing (𝓞 F) F)ˣ |
        ideleNorm F z' ^ 2 * ideleNorm F t ∈ Set.Icc a b} from h), enorm_zero]

  have h2 : ‖I.indicator (fun _ => (1 : ℂ)) (ideleNorm F t)‖ₑ =
      ENNReal.ofReal (I.indicator (fun _ => (1 : ℝ)) (ideleNorm F t)) := by
    by_cases h : ideleNorm F t ∈ I
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, enorm_one, ENNReal.ofReal_one]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, enorm_zero, ENNReal.ofReal_zero]

  have h3 : ‖(((etaFst μ α hα s (z * t) : ℂˣ) : ℂ) * ((etaSnd ν α hα s z : ℂˣ) : ℂ) *
        φ (k : AdelicGL2 (𝓞 F) F))‖ₑ =
      ENNReal.ofReal (ideleNorm F t ^ (s.re + 1 / 2)) * ‖φ (k : AdelicGL2 (𝓞 F) F)‖ₑ := by
    rw [enorm_mul, ← ofReal_norm (((etaFst μ α hα s (z * t) : ℂˣ) : ℂ) * _),
      norm_eta_pair F α hα hαN hμ hν]
  have h4 : ‖(starRingEnd ℂ) (((etaFst μ' α hα s' (z * t) : ℂˣ) : ℂ) * ((etaSnd ν' α hα s' z : ℂˣ) : ℂ) *
        φ' (k : AdelicGL2 (𝓞 F) F))‖ₑ =
      ENNReal.ofReal (ideleNorm F t ^ (s'.re + 1 / 2)) * ‖φ' (k : AdelicGL2 (𝓞 F) F)‖ₑ := by
    rw [← ofReal_norm, RCLike.norm_conj, ofReal_norm, enorm_mul,
      ← ofReal_norm (((etaFst μ' α hα s' (z * t) : ℂˣ) : ℂ) * _), norm_eta_pair F α hα hαN hμ' hν']
  rw [enorm_mul, enorm_mul, enorm_mul, h1, h2, h3, h4]

  have hpow : ENNReal.ofReal (ideleNorm F t ^ (s.re + 1 / 2)) * ENNReal.ofReal (ideleNorm F t ^ (s'.re + 1 / 2)) *
      ENNReal.ofReal ((ideleNorm F t)⁻¹) = ENNReal.ofReal (ideleNorm F t ^ (s.re + s'.re)) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le _), ← ENNReal.ofReal_mul
      (mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.rpow_nonneg ht0.le _))]
    congr 1
    rw [← Real.rpow_add ht0, ← Real.rpow_neg_one, ← Real.rpow_add ht0]
    congr 1
    ring
  rw [ENNReal.ofReal_mul (Set.indicator_nonneg (fun _ _ => zero_le_one) _), ← hpow]
  ring

end Integrand

section Finite

variable (F : Type) [Field F] [NumberField F]

theorem lintegral_separated_lt_top {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) (κ : Measure Z) [SFinite μ] [SFinite ν] [SFinite κ]
    (A : X → Y → ℝ≥0∞) (hA : Measurable (Function.uncurry A)) (G : Y → ℝ≥0∞) (hG : Measurable G)
    (Kf : Z → ℝ≥0∞) (hK : Measurable Kf)
    (C : ℝ≥0∞) (hC : ∀ y, ∫⁻ x, A x y ∂μ = C) (hCtop : C ≠ ⊤) (hGfin : ∫⁻ y, G y ∂ν < ⊤)
    (hKfin : ∫⁻ z, Kf z ∂κ < ⊤) :
    ∫⁻ x, ∫⁻ y, ∫⁻ z, A x y * G y * Kf z ∂κ ∂ν ∂μ < ⊤ := by
  have hAG : Measurable (Function.uncurry fun x y => A x y * G y) := hA.mul (hG.comp measurable_snd)
  have hAy : ∀ y, Measurable fun x => A x y := fun y => hA.comp (measurable_id.prodMk measurable_const)
  have hAx : ∀ x, Measurable fun y => A x y * G y := fun x => (hA.comp (measurable_const.prodMk measurable_id)).mul hG
  simp_rw [lintegral_const_mul _ hK]
  have h1 : ∀ x, ∫⁻ y, A x y * G y * ∫⁻ z, Kf z ∂κ ∂ν = (∫⁻ y, A x y * G y ∂ν) * ∫⁻ z, Kf z ∂κ :=
    fun x => lintegral_mul_const _ (hAx x)
  simp_rw [h1]
  have hm : Measurable fun x => ∫⁻ y, A x y * G y ∂ν := hAG.lintegral_prod_right'
  have hswap : ∫⁻ x, ∫⁻ y, A x y * G y ∂ν ∂μ = ∫⁻ y, ∫⁻ x, A x y * G y ∂μ ∂ν :=
    lintegral_lintegral_swap hAG.aemeasurable
  rw [lintegral_mul_const _ hm, hswap]
  have h2 : ∀ y, ∫⁻ x, A x y * G y ∂μ = C * G y := fun y => by rw [lintegral_mul_const _ (hAy y), hC]
  simp_rw [h2]
  rw [lintegral_const_mul _ hG]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hCtop.lt_top hGfin) hKfin

theorem Icc_self_eq_iInter (α : ℝ) :
    Set.Icc α α = ⋂ n : ℕ, Set.Icc α (α + 1 / ((n : ℝ) + 1)) := by
  ext y
  simp only [Set.mem_Icc, Set.mem_iInter]
  constructor
  · rintro ⟨h1, h2⟩ n
    exact ⟨h1, h2.trans (le_add_of_nonneg_right (by positivity))⟩
  · intro h
    refine ⟨(h 0).1, le_of_forall_pos_le_add fun ε hε => ?_⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact (h n).2.trans (by linarith)

theorem measurableSet_sqShell (a b r : ℝ) :
    MeasurableSet {z : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F z ^ 2 * r ∈ Set.Icc a b} :=
  (((NumberField.TateGlobal.continuous_ideleNorm F).pow 2).mul continuous_const).measurable measurableSet_Icc

theorem exists_shell_const (a b : ℝ) (ha : 0 < a) (D : Set (AdeleRing (𝓞 F) F)ˣ) (hD : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ r : ℝ, 0 < r →
      NumberField.Idele.idelicHaar F (D ∩ {z : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F z ^ 2 * r ∈ Set.Icc a b}) = C := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · obtain ⟨C, -, hCtop, hC⟩ :=
      NumberField.Idele.exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const F D hD hDF a b ha hab
    exact ⟨C, hCtop, hC⟩
  · have hpos : ∀ n : ℕ, a < a + 1 / ((n : ℝ) + 1) := fun n => lt_add_of_pos_right _ (by positivity)
    choose C hC0 hCtop hC using fun n : ℕ =>
      NumberField.Idele.exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const F D hD hDF a
        (a + 1 / ((n : ℝ) + 1)) ha (hpos n)
    refine ⟨⨅ n, C n, ne_top_of_le_ne_top (hCtop 0) (iInf_le _ 0), fun r hr => ?_⟩
    have hset : D ∩ {z : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F z ^ 2 * r ∈ Set.Icc a a} =
        ⋂ n : ℕ, (D ∩ {z : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F z ^ 2 * r ∈ Set.Icc a (a + 1 / ((n : ℝ) + 1))}) := by
      rw [← Set.inter_iInter]
      congr 1
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Icc_self_eq_iInter a]
    rw [hset]
    have hanti : Antitone fun n : ℕ =>
        D ∩ {z : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F z ^ 2 * r ∈ Set.Icc a (a + 1 / ((n : ℝ) + 1))} := by
      intro m n hmn
      refine Set.inter_subset_inter_right _ fun u hu => ⟨hu.1, hu.2.trans ?_⟩
      have h1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have h2 : ((m : ℝ) + 1) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hmn
      exact add_le_add_right (one_div_le_one_div_of_le h1 h2) _
    rw [hanti.measure_iInter (fun n => (hD.inter (measurableSet_sqShell F _ _ r)).nullMeasurableSet)
      ⟨0, by rw [hC 0 r hr]; exact hCtop 0⟩]
    exact iInf_congr fun n => hC n r hr
  · refine ⟨0, ENNReal.zero_ne_top, fun r hr => ?_⟩
    have hempty : {z : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F z ^ 2 * r ∈ Set.Icc a b} = ∅ := by
      ext z
      simp [Set.Icc_eq_empty_of_lt hba]
    rw [hempty, Set.inter_empty, measure_empty]

theorem lintegral_Ioi_indicator_rpow (I : Set ℝ) (hI : MeasurableSet I) (p : ℝ) :
    ∫⁻ y in Set.Ioi (0 : ℝ), ENNReal.ofReal (I.indicator (fun _ => (1 : ℝ)) y * y ^ p) * ENNReal.ofReal y⁻¹ =
      ∫⁻ y in I ∩ Set.Ioi 0, ENNReal.ofReal (y ^ (p - 1)) := by
  rw [← Measure.restrict_restrict hI, ← lintegral_indicator hI]
  refine setLIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : (0 : ℝ) < y := hy
  by_cases h : y ∈ I
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hy0.le _), Real.rpow_sub_one hy0.ne', div_eq_mul_inv]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul, ENNReal.ofReal_zero, zero_mul]

theorem lintegral_word_lt_top (a b : ℝ) (ha : 0 < a) {I : Set ℝ} (hI : MeasurableSet I)
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαN : ∀ x, ((α x : ℝˣ) : ℝ) = ideleNorm F x)
    {μ ν μ' ν' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (hμ' : IsUnitaryChar (𝓞 F) F μ') (hν' : IsUnitaryChar (𝓞 F) F ν')
    (s s' : ℂ) {φ φ' : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
    (hφ' : IsInducedSection (𝓞 F) F (etaFst μ' α hα s') (etaSnd ν' α hα s') φ')
    (hφc : Continuous φ) (hφ'c : Continuous φ')
    (D D' : Set (AdeleRing (𝓞 F) F)ˣ) (hD : MeasurableSet D) (hD' : MeasurableSet D')
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (hD'F : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F))
    (hIint : ∫⁻ y in I ∩ Set.Ioi 0, ENNReal.ofReal (y ^ (s.re + s'.re - 1)) < ∞) :
    ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
        ‖integrand F a b I φ φ' (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F))‖ₑ *
          ENNReal.ofReal ((ideleNorm F t)⁻¹)
        ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) < ⊤ := by
  haveI := secondCountableTopology_idele F
  haveI := sigmaFinite_idelicHaar F
  simp_rw [enorm_integrand_word_mul F a b I α hα hαN hμ hν hμ' hν' s s' hφ hφ']
  have hN := (NumberField.TateGlobal.continuous_ideleNorm F).measurable

  obtain ⟨C, hCtop, hC⟩ := exists_shell_const F a b ha D hD hDF

  obtain ⟨V, -, hVtop, hV⟩ := NumberField.Idele.exists_setLIntegral_comp_ideleNorm_eq_mul_lintegral_Ioi F D' hD' hD'F
  refine lintegral_separated_lt_top ((NumberField.Idele.idelicHaar F).restrict D)
    ((NumberField.Idele.idelicHaar F).restrict D') (maximalCompactHaar F)
    (fun z t => {z' : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F z' ^ 2 * ideleNorm F t ∈ Set.Icc a b}.indicator
      (fun _ => (1 : ℝ≥0∞)) z) ?_
    (fun t => ENNReal.ofReal (I.indicator (fun _ => (1 : ℝ)) (ideleNorm F t) * ideleNorm F t ^ (s.re + s'.re))) ?_
    (fun k => ‖φ (k : AdelicGL2 (𝓞 F) F)‖ₑ * ‖φ' (k : AdelicGL2 (𝓞 F) F)‖ₑ) ?_ C ?_ hCtop ?_ ?_
  ·
    have hset : MeasurableSet {p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ |
        ideleNorm F p.1 ^ 2 * ideleNorm F p.2 ∈ Set.Icc a b} :=
      (((hN.comp measurable_fst).pow_const 2).mul (hN.comp measurable_snd)) measurableSet_Icc
    have heq : (Function.uncurry fun z t : (AdeleRing (𝓞 F) F)ˣ =>
        {z' : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F z' ^ 2 * ideleNorm F t ∈ Set.Icc a b}.indicator
          (fun _ => (1 : ℝ≥0∞)) z) =
        {p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ |
          ideleNorm F p.1 ^ 2 * ideleNorm F p.2 ∈ Set.Icc a b}.indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext p
      simp only [Function.uncurry, Set.indicator_apply, Set.mem_setOf_eq]
    rw [heq]
    exact measurable_const.indicator hset
  · exact ENNReal.measurable_ofReal.comp (((measurable_const.indicator hI).comp hN).mul (hN.pow_const _))
  · exact (hφc.comp continuous_subtype_val).measurable.enorm.mul (hφ'c.comp continuous_subtype_val).measurable.enorm
  · intro t
    beta_reduce
    rw [lintegral_indicator_const (measurableSet_sqShell F a b _), one_mul,
      Measure.restrict_apply (measurableSet_sqShell F a b _), Set.inter_comm]
    exact hC _ (ideleNorm_pos t)
  ·
    have hf : Measurable fun y : ℝ => ENNReal.ofReal (I.indicator (fun _ => (1 : ℝ)) y * y ^ (s.re + s'.re)) :=
      ENNReal.measurable_ofReal.comp ((measurable_const.indicator hI).mul (measurable_id.pow_const _))
    have h := hV _ hf
    beta_reduce at h
    rw [h, lintegral_Ioi_indicator_rpow I hI]
    exact ENNReal.mul_lt_top hVtop.lt_top hIint
  ·
    obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn
      ((hφc.comp continuous_subtype_val).continuousOn (s := (Set.univ : Set (adelicMaximalCompact F))))
    obtain ⟨M', hM'⟩ := isCompact_univ.exists_bound_of_continuousOn
      ((hφ'c.comp continuous_subtype_val).continuousOn (s := (Set.univ : Set (adelicMaximalCompact F))))
    have hbd : ∀ k : adelicMaximalCompact F,
        ‖φ (k : AdelicGL2 (𝓞 F) F)‖ₑ * ‖φ' (k : AdelicGL2 (𝓞 F) F)‖ₑ ≤ ENNReal.ofReal (M * M') := by
      intro k
      have h1 : ‖φ (k : AdelicGL2 (𝓞 F) F)‖ ≤ M := hM k (Set.mem_univ k)
      have h2 : ‖φ' (k : AdelicGL2 (𝓞 F) F)‖ ≤ M' := hM' k (Set.mem_univ k)
      have hM0 : 0 ≤ M := (norm_nonneg _).trans h1
      rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul h1 h2 (norm_nonneg _) hM0)
    refine lt_of_le_of_lt (lintegral_mono hbd) ?_
    rw [lintegral_const, measure_univ, mul_one]
    exact ENNReal.ofReal_lt_top

theorem iterated_integral_eq (a b : ℝ) (I : Set ℝ)
    {χ₁ χ₂ χ₁' χ₂' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {φ φ' : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ) (hφ' : IsInducedSection (𝓞 F) F χ₁' χ₂' φ')
    (D D' : Set (AdeleRing (𝓞 F) F)ˣ) :
    (∫ z in D, ∫ t in D', ∫ k,
        integrand F a b I φ φ' (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
          (((ideleNorm F t)⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)) =
      (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * (starRingEnd ℂ) (φ' (k : AdelicGL2 (𝓞 F) F)) ∂(maximalCompactHaar F)) *
        ∫ z in D, ∫ t in D',
            ((χ₁ (z * t) : ℂˣ) : ℂ) * ((χ₂ z : ℂˣ) : ℂ) *
              (starRingEnd ℂ) (((χ₁' (z * t) : ℂˣ) : ℂ) * ((χ₂' z : ℂˣ) : ℂ)) *
              (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t) *
              I.indicator (fun _ => (1 : ℂ)) (ideleNorm F t) *
              (((ideleNorm F t)⁻¹ : ℝ) : ℂ)
          ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) := by
  have hpt : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      integrand F a b I φ φ' (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
          (((ideleNorm F t)⁻¹ : ℝ) : ℂ) =
        (((χ₁ (z * t) : ℂˣ) : ℂ) * ((χ₂ z : ℂˣ) : ℂ) *
              (starRingEnd ℂ) (((χ₁' (z * t) : ℂˣ) : ℂ) * ((χ₂' z : ℂˣ) : ℂ)) *
              (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t) *
              I.indicator (fun _ => (1 : ℂ)) (ideleNorm F t) *
              (((ideleNorm F t)⁻¹ : ℝ) : ℂ)) *
          (φ (k : AdelicGL2 (𝓞 F) F) * (starRingEnd ℂ) (φ' (k : AdelicGL2 (𝓞 F) F))) := by
    intro z t k
    rw [integrand_word F a b I hφ hφ']
    simp only [map_mul]
    ring
  simp_rw [hpt, integral_const_mul, integral_mul_const]
  rw [mul_comm]

end Finite

end KcWindow

end

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal
open scoped NNReal ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (c : ℝ≥0∞) (hc_top : c ≠ ∞)
      (hc : ∀ (D D' : Set (AdeleRing (𝓞 F) F)ˣ), MeasurableSet D → MeasurableSet D' →
          IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F) →
          IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F) →
        ∀ f : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable f →
          (∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (x * g) = f g) →
          ∫⁻ q, f q.out ∂(rationalTorusUnipotentQuotientMeasure F) =
            c * ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
                  f (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
                    ENNReal.ofReal ((ideleNorm F t)⁻¹)
                ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F))
      (D D' : Set (AdeleRing (𝓞 F) F)ˣ) (hD : MeasurableSet D) (hD' : MeasurableSet D')
      (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
      (hD'F : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F))
      (μ ν μ' ν' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
      (hμ' : IsUnitaryChar (𝓞 F) F μ') (hν' : IsUnitaryChar (𝓞 F) F ν')
      (hμF : IsIdeleClassChar (𝓞 F) F μ) (hνF : IsIdeleClassChar (𝓞 F) F ν)
      (hμ'F : IsIdeleClassChar (𝓞 F) F μ') (hν'F : IsIdeleClassChar (𝓞 F) F ν')
      (s s' : ℂ) (φ φ' : AdelicGL2 (𝓞 F) F → ℂ)
      (hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (hφ' : IsInducedSection (𝓞 F) F (etaFst μ' α hα s') (etaSnd ν' α hα s') φ')
      (hφc : Continuous φ) (hφ'c : Continuous φ')
      (a b : ℝ) (ha : 0 < a) (I : Set ℝ) (hI : MeasurableSet I)
      (hIint : ∫⁻ y in I ∩ Set.Ioi 0, ENNReal.ofReal (y ^ (s.re + s'.re - 1)) < ∞),
    Integrable (fun q : RationalTorusUnipotentQuotient F =>
        {g : AdelicGL2 (𝓞 F) F |
            NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}.indicator
          (fun _ => (1 : ℂ)) q.out *
          I.indicator (fun _ => (1 : ℂ))
            (NumberField.AdelicHeight.adelicHeight F q.out) *
          (φ q.out * (starRingEnd ℂ) (φ' q.out)))
      (rationalTorusUnipotentQuotientMeasure F) ∧
    ∫ q : RationalTorusUnipotentQuotient F,
        {g : AdelicGL2 (𝓞 F) F |
            NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}.indicator
          (fun _ => (1 : ℂ)) q.out *
          I.indicator (fun _ => (1 : ℂ))
            (NumberField.AdelicHeight.adelicHeight F q.out) *
          (φ q.out * (starRingEnd ℂ) (φ' q.out))
        ∂(rationalTorusUnipotentQuotientMeasure F) =
      (c.toReal : ℂ) *
        (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * (starRingEnd ℂ) (φ' (k : AdelicGL2 (𝓞 F) F))
          ∂(maximalCompactHaar F)) *
        ∫ z in D, ∫ t in D',
            ((etaFst μ α hα s (z * t) : ℂˣ) : ℂ) * ((etaSnd ν α hα s z : ℂˣ) : ℂ) *
              (starRingEnd ℂ) (((etaFst μ' α hα s' (z * t) : ℂˣ) : ℂ) * ((etaSnd ν' α hα s' z : ℂˣ) : ℂ)) *
              (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t) *
              I.indicator (fun _ => (1 : ℂ)) (ideleNorm F t) *
              (((ideleNorm F t)⁻¹ : ℝ) : ℂ)
          ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) := by
  intro α hα c hc_top hc D D' hD hD' hDF hD'F μ ν μ' ν' hμ hν hμ' hν' hμF hνF hμ'F hν'F s s' φ φ' hφ hφ' hφc hφ'c a b ha
    I hI hIint
  have hαN : ∀ x, ((α x : ℝˣ) : ℝ) = ideleNorm F x := fun x => rfl
  obtain ⟨hint, heq⟩ := KcWindow.integrable_and_integral_eq_of_lintegral F c hc_top hc D D' hD hD' hDF hD'F
    (KcWindow.integrand F a b I φ φ') (KcWindow.measurable_integrand F a b hI hφc hφ'c)
    (KcWindow.integrand_mul_of_mem F a b I α hα hαN μ ν μ' ν' hμF hνF hμ'F hν'F s s' hφ hφ')
    (KcWindow.lintegral_word_lt_top F a b ha hI α hα hαN hμ hν hμ' hν' s s' hφ hφ' hφc hφ'c D D' hD hD' hDF hD'F
      hIint)
  refine ⟨hint, heq.trans ?_⟩
  rw [KcWindow.iterated_integral_eq F a b I hφ hφ' D D', ← mul_assoc]

end S_AutomorphicForm_integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa_of_window
end P2MW
export P2MW.S_AutomorphicForm_integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa_of_window (solution)
