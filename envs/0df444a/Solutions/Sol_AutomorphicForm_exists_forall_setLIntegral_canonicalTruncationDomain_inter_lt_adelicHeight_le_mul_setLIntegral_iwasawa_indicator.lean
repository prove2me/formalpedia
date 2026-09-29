-- Prove2me | solution 1 for AutomorphicForm.exists_forall_setLIntegral_canonicalTruncationDomain_inter_lt_adelicHeight_le_mul_setLIntegral_iwasawa_indicator
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/c3857d44-3c51-5574-b91d-1eb5e7aa7b45

import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Theorems.Thm_AutomorphicForm_exists_forall_setLIntegral_tsum_borelSubgroup_cosets_eq_mul_lintegral_iwasawa
import Theorems.Thm_AutomorphicForm_isFundamentalDomain_boxSheet_rationalTorusUnipotent
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_unipotentGL2_mul_and_centralScalar_mul
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_mem_borelSubgroup
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_setLIntegral_canonicalTruncationDomain_inter_lt_adelicHeight_le_mul_setLIntegral_iwasawa_indicator
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi"
p2m_attr_erase "simp" "LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul LocalGL2.swapUnit_val AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.mem_inducedSectionSubmodule_iff"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open NumberField.AdelicBox
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem solution
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    ∃ c₀ : ℝ≥0∞, c₀ ≠ ∞ ∧
      ∀ (D D' : Set (AdeleRing (𝓞 K) K)ˣ), MeasurableSet D → MeasurableSet D' →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K) →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D' (NumberField.Idele.idelicHaar K) →
      ∀ (T : ℝ) (F : AdelicGL2 (𝓞 K) K → ℝ≥0∞), Measurable F →
        (∀ x ∈ rationalTorusUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, F (x * g) = F g) →
        ∫⁻ g in AutomorphicForm.canonicalTruncationDomain K α β ∩
            {g | T < NumberField.AdelicHeight.adelicHeight K g}, F g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) ≤
          c₀ * ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
              ({g : AdelicGL2 (𝓞 K) K |
                    NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} ∩
                  {g | T < NumberField.AdelicHeight.adelicHeight K g}).indicator F
                  (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
                ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
            ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) := by
  classical
  obtain ⟨c, -, hctop, hunf, -⟩ :=
    AutomorphicForm.exists_forall_setLIntegral_tsum_borelSubgroup_cosets_eq_mul_lintegral_iwasawa K
  have hbox : adelicAddHaar (𝓞 K) K (adelicBox K) ≠ ∞ := (adelicAddHaar_adelicBox_lt_top (K := K)).ne
  refine ⟨c * adelicAddHaar (𝓞 K) K (adelicBox K), ENNReal.mul_ne_top hctop hbox, ?_⟩
  intro D D' hD hD' hDF hD'F T F hF hinv

  set S₀ : Set (AdelicGL2 (𝓞 K) K) :=
    {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} with hS₀def
  set W : Set (AdelicGL2 (𝓞 K) K) := {g | T < NumberField.AdelicHeight.adelicHeight K g} with hWdef
  have hS₀m : MeasurableSet S₀ :=
    (isClosed_Icc.preimage (NumberField.TateGlobal.continuous_ideleNorm_det K)).measurableSet
  have hWm : MeasurableSet W :=
    (isOpen_lt continuous_const (NumberField.AdelicHeight.continuous_adelicHeight K)).measurableSet
  have hS₀inv : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      globalPoints (𝓞 K) K γ * g ∈ S₀ ↔ g ∈ S₀ := by
    intro γ g
    simp only [hS₀def, Set.mem_setOf_eq, map_mul, NumberField.TateGlobal.ideleNorm_mul,
      AutomorphicForm.ideleNorm_det_globalPoints, one_mul]
  obtain ⟨-, -, -, hΦS, hΦfd⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ

  let Bk : Subgroup (GL (Fin 2) K) := borelSubgroup K
  let reps : Set (GL (Fin 2) K) := Set.range (fun q : Quotient (QuotientGroup.rightRel Bk) => q.out)
  have hreps : ∀ g : GL (Fin 2) K, ∃! ρ : GL (Fin 2) K, ρ ∈ reps ∧ g * ρ⁻¹ ∈ borelSubgroup K := by
    intro g
    refine ⟨(Quotient.mk (QuotientGroup.rightRel Bk) g).out, ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
    · have h := Quotient.mk_out (s := QuotientGroup.rightRel Bk) g
      exact QuotientGroup.rightRel_apply.mp h
    · rintro ρ ⟨⟨q, rfl⟩, hq⟩
      have hq' : q = Quotient.mk (QuotientGroup.rightRel Bk) g := by
        rw [← Quotient.out_eq q]
        exact Quotient.sound (QuotientGroup.rightRel_apply.mpr hq)
      rw [hq']

  have hBle : (borelSubgroup K).map (globalPoints (𝓞 K) K) ≤ rationalTorusUnipotent K :=
    (AutomorphicForm.isFundamentalDomain_boxSheet_rationalTorusUnipotent K).1
  have hHinv := NumberField.AdelicHeight.adelicHeight_unipotentGL2_mul_and_centralScalar_mul K
  set F' : AdelicGL2 (𝓞 K) K → ℝ≥0∞ := W.indicator F with hF'def
  have hF'm : Measurable F' := hF.indicator hWm
  have hF'inv : ∀ b ∈ borelSubgroup K, ∀ g : AdelicGL2 (𝓞 K) K,
      F' (globalPoints (𝓞 K) K b * g) = F' g := by
    intro b hb g
    have hmem : globalPoints (𝓞 K) K b ∈ rationalTorusUnipotent K :=
      hBle (Subgroup.mem_map.mpr ⟨b, hb, rfl⟩)
    have hW : globalPoints (𝓞 K) K b * g ∈ W ↔ g ∈ W := by
      simp only [hWdef, Set.mem_setOf_eq,
        NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_mem_borelSubgroup K hb g]
    simp only [hF'def, Set.indicator]
    by_cases hg : g ∈ W
    · rw [if_pos (hW.mpr hg), if_pos hg, hinv _ hmem g]
    · rw [if_neg (fun h => hg (hW.mp h)), if_neg hg]
  have key := hunf S₀ hS₀m hS₀inv (AutomorphicForm.canonicalTruncationDomain K α β) hΦS hΦfd reps hreps
    (adelicBox K) D D' (isAddFundamentalDomain_adelicBox_adelicAddHaar (K := K)) hDF hD'F F' hF'm hF'inv

  obtain ⟨ρ₀, ⟨hρ₀, hρ₀B⟩, -⟩ := hreps 1
  have hρ₀B' : ρ₀ ∈ borelSubgroup K := by
    rw [one_mul] at hρ₀B
    exact (Subgroup.inv_mem_iff _).mp hρ₀B

  have hdetU : ∀ x : AdeleRing (𝓞 K) K, Matrix.GeneralLinearGroup.det
      (unipotentGL2 x : AdelicGL2 (𝓞 K) K) = 1 := by
    intro x
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have hUmem : ∀ x : AdeleRing (𝓞 K) K,
      (unipotentGL2 x : AdelicGL2 (𝓞 K) K) ∈ rationalTorusUnipotent K :=
    fun x => Subgroup.mem_sup_right ⟨Multiplicative.ofAdd x, rfl⟩
  have hpt : ∀ (x : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K),
      S₀.indicator F' (unipotentGL2 x * g) = (S₀ ∩ W).indicator F g := by
    intro x g
    rw [hF'def, Set.indicator_indicator]
    have hS : unipotentGL2 x * g ∈ S₀ ∩ W ↔ g ∈ S₀ ∩ W := by
      simp only [hS₀def, hWdef, Set.mem_inter_iff, Set.mem_setOf_eq, map_mul, hdetU, one_mul,
        hHinv.1 x g]
    simp only [Set.indicator]
    by_cases hg : g ∈ S₀ ∩ W
    · rw [if_pos (hS.mpr hg), if_pos hg, hinv _ (hUmem x) g]
    · rw [if_neg (fun h => hg (hS.mp h)), if_neg hg]

  have hLHS : ∫⁻ g in AutomorphicForm.canonicalTruncationDomain K α β ∩ W, F g
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      = ∫⁻ g in AutomorphicForm.canonicalTruncationDomain K α β, F' g
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    rw [hF'def, setLIntegral_indicator hWm, Set.inter_comm]
  set I : ℝ≥0∞ := ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
      (S₀ ∩ W).indicator F (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
        ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
      ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) with hIdef
  calc ∫⁻ g in AutomorphicForm.canonicalTruncationDomain K α β ∩ W, F g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      = ∫⁻ g in AutomorphicForm.canonicalTruncationDomain K α β, F' g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := hLHS
    _ ≤ ∫⁻ x in AutomorphicForm.canonicalTruncationDomain K α β,
          ∑' ρ : reps, F' (globalPoints (𝓞 K) K (ρ : GL (Fin 2) K) * x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
        refine lintegral_mono (fun x => ?_)
        calc F' x = F' (globalPoints (𝓞 K) K ρ₀ * x) := (hF'inv ρ₀ hρ₀B' x).symm
          _ ≤ ∑' ρ : reps, F' (globalPoints (𝓞 K) K (ρ : GL (Fin 2) K) * x) :=
            ENNReal.le_tsum (⟨ρ₀, hρ₀⟩ : reps)
    _ = c * ∫⁻ x in adelicBox K, I ∂(adelicAddHaar (𝓞 K) K) := by
        rw [key, hIdef]
        congr 1
        refine lintegral_congr (fun x => ?_)
        simp only [mul_assoc, hpt]
    _ = c * (I * adelicAddHaar (𝓞 K) K (adelicBox K)) := by rw [setLIntegral_const]
    _ = c * adelicAddHaar (𝓞 K) K (adelicBox K) * I := by ring

end S_AutomorphicForm_exists_forall_setLIntegral_canonicalTruncationDomain_inter_lt_adelicHeight_le_mul_setLIntegral_iwasawa_indicator
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_setLIntegral_canonicalTruncationDomain_inter_lt_adelicHeight_le_mul_setLIntegral_iwasawa_indicator (solution)
