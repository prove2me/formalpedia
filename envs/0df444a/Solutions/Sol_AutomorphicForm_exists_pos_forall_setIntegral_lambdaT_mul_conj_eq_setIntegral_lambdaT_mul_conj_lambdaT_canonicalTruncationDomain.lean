-- Prove2me | solution 1 for AutomorphicForm.exists_pos_forall_setIntegral_lambdaT_mul_conj_eq_setIntegral_lambdaT_mul_conj_lambdaT_canonicalTruncationDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/7f60eb1f-a41c-52de-8324-d26903954ae8

import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_AutomorphicForm_exists_pos_forall_setIntegral_sub_constantTerm_mul_eq_zero_canonicalTruncationDomain_inter_lt_adelicHeight
import Theorems.Thm_AutomorphicForm_constantTerm_adelicBox_unipotentGL2_mul
import Theorems.Thm_AutomorphicForm_constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_pos_forall_setIntegral_lambdaT_mul_conj_eq_setIntegral_lambdaT_mul_conj_lambdaT_canonicalTruncationDomain
p2m_attr_erase "instance" "FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add AutomorphicForm.mem_inducedSectionSubmodule_iff M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicHeight NumberField.AdelicBox
open AutomorphicForm
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

namespace R1TruncProj

variable (K : Type) [Field K] [NumberField K]

theorem measurable_constantTerm (ν : Measure (AdeleRing (𝓞 K) K)) [SFinite ν]
    {a : AdelicGL2 (𝓞 K) K → ℂ} (ha : Measurable a) :
    Measurable (constantTerm ν (fun x => unipotentGL2 x) a) := by
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
  have hcont : Continuous fun p : AdelicGL2 (𝓞 K) K × AdeleRing (𝓞 K) K => unipotentGL2 p.2 * p.1 :=
    (AutomorphicForm.continuous_unipotentGL2.comp continuous_snd).mul continuous_fst
  have hF : StronglyMeasurable fun p : AdelicGL2 (𝓞 K) K × AdeleRing (𝓞 K) K => a (unipotentGL2 p.2 * p.1) :=
    (ha.comp hcont.measurable).stronglyMeasurable
  have := hF.integral_prod_right' (ν := ν)
  exact this.measurable

theorem unipotentGL2_mem_borelSubgroup {R : Type*} [CommRing R] (x : R) :
    unipotentGL2 x ∈ borelSubgroup R := by
  simp [mem_borelSubgroup_iff]

theorem main (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ (a b : AdelicGL2 (𝓞 K) K → ℂ), Measurable a → Measurable b →
        (∀ γ ∈ borelSubgroup K, ∀ g : AdelicGL2 (𝓞 K) K, a (globalPoints (𝓞 K) K γ * g) = a g) →
        (∀ γ ∈ borelSubgroup K, ∀ g : AdelicGL2 (𝓞 K) K, b (globalPoints (𝓞 K) K γ * g) = b g) →
        IntegrableOn
          (fun g => lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
              (fun x => unipotentGL2 x) (adelicHeight K) T a g * conj (b g))
          (canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) →
        IntegrableOn
          (fun g => lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
              (fun x => unipotentGL2 x) (adelicHeight K) T a g *
            conj (lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
              (fun x => unipotentGL2 x) (adelicHeight K) T b g))
          (canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) →
        ∫ g in canonicalTruncationDomain K α β,
            lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
              (fun x => unipotentGL2 x) (adelicHeight K) T a g * conj (b g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
          = ∫ g in canonicalTruncationDomain K α β,
            lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
              (fun x => unipotentGL2 x) (adelicHeight K) T a g *
            conj (lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
              (fun x => unipotentGL2 x) (adelicHeight K) T b g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  obtain ⟨T₀, hT₀, hV⟩ :=
    AutomorphicForm.exists_pos_forall_setIntegral_sub_constantTerm_mul_eq_zero_canonicalTruncationDomain_inter_lt_adelicHeight
      K α β hα hαβ
  refine ⟨T₀, hT₀, fun T hT a b ha hb haB hbB h1 h2 => ?_⟩

  set μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set Φ₀ := canonicalTruncationDomain K α β with hΦ₀
  set hi : Set (AdelicGL2 (𝓞 K) K) := {g | T < adelicHeight K g} with hhi
  set ν : Measure (AdeleRing (𝓞 K) K) := ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K) with hν
  set aN : AdelicGL2 (𝓞 K) K → ℂ := constantTerm ν (fun x => unipotentGL2 x) a with haN
  set bN : AdelicGL2 (𝓞 K) K → ℂ := constantTerm ν (fun x => unipotentGL2 x) b with hbN
  set d : AdelicGL2 (𝓞 K) K → ℂ := fun g => conj (bN g) with hd
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_cond_adelicBox K
  have hhi_m : MeasurableSet hi :=
    measurableSet_lt measurable_const (NumberField.AdelicHeight.continuous_adelicHeight K).measurable

  have hbN_m : Measurable bN := measurable_constantTerm K ν hb
  have hd_m : Measurable d := Complex.continuous_conj.measurable.comp hbN_m
  have hdB : ∀ γ ∈ borelSubgroup K, ∀ g : AdelicGL2 (𝓞 K) K, d (globalPoints (𝓞 K) K γ * g) = d g := by
    intro γ hγ g
    simp only [hd, hbN]
    rw [AutomorphicForm.constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup K hbB hγ g]
  have hdN : ∀ (x : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), d (unipotentGL2 x * g) = d g := by
    intro x g
    simp only [hd, hbN]
    rw [AutomorphicForm.constantTerm_adelicBox_unipotentGL2_mul K
      (fun k h => hbB _ (unipotentGL2_mem_borelSubgroup k) h) x g]

  set F' : AdelicGL2 (𝓞 K) K → ℂ := fun g => (a g - aN g) * d g with hF'
  set D : AdelicGL2 (𝓞 K) K → ℂ := fun g =>
    lambdaT ν (fun x => unipotentGL2 x) (adelicHeight K) T a g * conj (b g) -
      lambdaT ν (fun x => unipotentGL2 x) (adelicHeight K) T a g *
        conj (lambdaT ν (fun x => unipotentGL2 x) (adelicHeight K) T b g) with hD
  have hDF : D = hi.indicator F' := by
    funext g
    by_cases hg : g ∈ hi
    · have hg' : T < adelicHeight K g := hg
      rw [Set.indicator_of_mem hg, hD, hF']
      simp only [lambdaT_apply_of_lt _ _ hg', hd, map_sub]
      ring
    · have hg' : adelicHeight K g ≤ T := not_lt.1 hg
      rw [Set.indicator_of_notMem hg, hD]
      simp only [lambdaT_apply_of_le _ _ hg', sub_self]

  have hDint : IntegrableOn D Φ₀ μ := h1.sub h2
  have hint : IntegrableOn F' (Φ₀ ∩ hi) μ := by
    rw [hDF, IntegrableOn, integrable_indicator_iff hhi_m] at hDint
    rw [IntegrableOn, Set.inter_comm, ← Measure.restrict_restrict hhi_m]
    exact hDint
  have h0 : ∫ g in Φ₀ ∩ hi, F' g ∂μ = 0 := hV T hT a d ha hd_m haB hdB hdN hint

  refine (sub_eq_zero.1 ?_)
  rw [← integral_sub h1 h2]
  change ∫ g in Φ₀, D g ∂μ = 0
  rw [hDF, setIntegral_indicator hhi_m]
  exact h0

end R1TruncProj

theorem solution
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ (a b : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ), Measurable a → Measurable b →
        (∀ γ ∈ AutomorphicForm.borelSubgroup K, ∀ g : AutomorphicForm.AdelicGL2 (𝓞 K) K,
          a (AutomorphicForm.globalPoints (𝓞 K) K γ * g) = a g) →
        (∀ γ ∈ AutomorphicForm.borelSubgroup K, ∀ g : AutomorphicForm.AdelicGL2 (𝓞 K) K,
          b (AutomorphicForm.globalPoints (𝓞 K) K γ * g) = b g) →
        IntegrableOn
          (fun g => AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
              (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight K) T a g *
            conj (b g))
          (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) →
        IntegrableOn
          (fun g => AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
              (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight K) T a g *
            conj (AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
              (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight K) T b g))
          (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
            AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
              (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight K) T a g *
            conj (b g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
          = ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
            AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
              (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight K) T a g *
            conj (AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
              (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight K) T b g)
              ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
  R1TruncProj.main K α β hα hαβ

end S_AutomorphicForm_exists_pos_forall_setIntegral_lambdaT_mul_conj_eq_setIntegral_lambdaT_mul_conj_lambdaT_canonicalTruncationDomain
end P2MW
export P2MW.S_AutomorphicForm_exists_pos_forall_setIntegral_lambdaT_mul_conj_eq_setIntegral_lambdaT_mul_conj_lambdaT_canonicalTruncationDomain (solution)
