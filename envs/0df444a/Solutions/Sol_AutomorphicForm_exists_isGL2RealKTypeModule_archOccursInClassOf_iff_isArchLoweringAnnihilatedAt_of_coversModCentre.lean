-- Prove2me | solution 1 for AutomorphicForm.exists_isGL2RealKTypeModule_archOccursInClassOf_iff_isArchLoweringAnnihilatedAt_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/43f3aaa9-5500-58b2-8789-5dbeb0c6174b

import Mathlib
import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchLoweringAnnihilated
import Definitions.Def_AutomorphicForm_GL2RealKTypeModule
import Theorems.Thm_AutomorphicForm_exists_archOccursInClassOf_archWeightChar_of_coversModCentre
import Theorems.Thm_AutomorphicForm_even_sub_of_archOccursInClassOf_archWeightChar
import Theorems.Thm_AutomorphicForm_archOccursInClassOf_archWeightChar_neg_of_coversModCentre
import Theorems.Thm_AutomorphicForm_archOccursInClassOf_archWeightChar_add_two_of_nonneg_of_coversModCentre
import Theorems.Thm_AutomorphicForm_one_le_of_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_not_archOccursInClassOf_archWeightChar_sub_two_of_isArchLoweringAnnihilatedAt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_not_archOccursInClassOf_archWeightChar_sub_two_of_coversModCentre
import Theorems.Thm_AutomorphicForm_exists_isIrreducibleGL2RealKTypeModule_ne_bot_iff_even_sub
import Theorems.Thm_AutomorphicForm_exists_isIrreducibleGL2RealKTypeModule_lower_eq_zero_iff_of_one_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isGL2RealKTypeModule_archOccursInClassOf_iff_isArchLoweringAnnihilatedAt_of_coversModCentre
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul"
p2m_attr_erase "instance" "IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply"
p2m_attr_erase "simp" "NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq AutomorphicForm.CuspidalConstituent.rightRegular_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.LDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal"
p2m_attr_erase "simp" "Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq"
p2m_attr_erase "simp" "FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq"

set_option autoImplicit false

p2m_open "NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm P2MW.S_AutomorphicForm_exists_isGL2RealKTypeModule_archOccursInClassOf_iff_isArchLoweringAnnihilatedAt_of_coversModCentre.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

namespace AutomorphicForm
p2m_export "AutomorphicForm" "ArchOccursInClassOf ArchOccursInClassOf.and_left AdelicGL2 HeckeEigensystem rowIsometrySubgroup₀Map norm_ringEquivRealOfIsReal archWeightCharℝ HasArchCharacterAt₀ IsArchLoweringAnnihilatedAt IsGL2RealKTypeModule IsIrreducibleGL2RealKTypeModule exists_archOccursInClassOf_archWeightChar_of_coversModCentre even_sub_of_archOccursInClassOf_archWeightChar archOccursInClassOf_archWeightChar_neg_of_coversModCentre archOccursInClassOf_archWeightChar_add_two_of_nonneg_of_coversModCentre one_le_of_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_coversModCentre not_archOccursInClassOf_archWeightChar_sub_two_of_isArchLoweringAnnihilatedAt_of_coversModCentre archOccursInClassOf_isArchLoweringAnnihilatedAt_of_not_archOccursInClassOf_archWeightChar_sub_two_of_coversModCentre exists_isIrreducibleGL2RealKTypeModule_ne_bot_iff_even_sub exists_isIrreducibleGL2RealKTypeModule_lower_eq_zero_iff_of_one_le"
namespace LocalComponentProfileAssembly
p2m_open "AutomorphicForm"

theorem profile (S Λ : ℤ → Prop)
    (h0 : ∃ n, S n)
    (h1 : ∀ n m, S n → S m → Even (n - m))
    (h2 : ∀ n, S n → S (-n))
    (h3 : ∀ n, 0 ≤ n → S n → S (n + 2))
    (h4a : ∀ k, Λ k → 1 ≤ k)
    (h4b : ∀ k, 2 ≤ k → Λ k → ¬ S (k - 2))
    (h5 : ∀ k, S k → ¬ S (k - 2) → Λ k)
    (hΛS : ∀ k, Λ k → S k) :
    ∃ m₀ : ℤ, 0 ≤ m₀ ∧
      (∀ n, S n ↔ (m₀ ≤ |n| ∧ Even (n - m₀))) ∧
      (∀ k, Λ k → k = m₀) ∧
      (Λ m₀ → 1 ≤ m₀) ∧
      (¬ Λ m₀ → ∀ n, S n ↔ Even (n - m₀)) := by
  classical

  have habs : ∀ n, S n → S (n.natAbs : ℤ) := by
    intro n hn
    rcases Int.natAbs_eq n with h | h
    · rwa [← h]
    · have := h2 n hn
      rwa [h, neg_neg] at this

  have hex : ∃ m : ℕ, S (m : ℤ) := by
    obtain ⟨n, hn⟩ := h0
    exact ⟨n.natAbs, habs n hn⟩
  set m₀ : ℕ := Nat.find hex with hm₀def
  have hm₀ : S (m₀ : ℤ) := Nat.find_spec hex
  have hmin : ∀ m : ℕ, S (m : ℤ) → m₀ ≤ m := fun m hm => Nat.find_min' hex hm

  have hup : ∀ j : ℕ, S ((m₀ : ℤ) + 2 * (j : ℤ)) := by
    intro j
    induction j with
    | zero => simpa using hm₀
    | succ j ih =>
      have := h3 _ (by positivity) ih
      have heq : (m₀ : ℤ) + 2 * (j : ℤ) + 2 = (m₀ : ℤ) + 2 * ((j + 1 : ℕ) : ℤ) := by
        push_cast; ring
      rwa [heq] at this

  have hS : ∀ n, S n ↔ ((m₀ : ℤ) ≤ |n| ∧ Even (n - m₀)) := by
    intro n
    constructor
    · intro hn
      refine ⟨?_, h1 n m₀ hn hm₀⟩
      have := hmin _ (habs n hn)
      rw [← Int.natCast_natAbs]
      exact_mod_cast this
    · rintro ⟨hle, r, hr⟩

      have hSabs : S (|n|) := by
        rcases Int.natAbs_eq n with h | h
        ·
          have hn0 : |n| = n := by
            rw [← Int.natCast_natAbs]; exact h.symm
          have hr0 : 0 ≤ r := by
            have : (m₀ : ℤ) ≤ n := by rwa [hn0] at hle
            omega
          have := hup r.toNat
          rw [Int.toNat_of_nonneg hr0] at this
          rw [hn0]
          convert this using 1
          omega
        ·
          have hn0 : |n| = -n := by
            rw [← Int.natCast_natAbs]; omega

          have hr' : -n - m₀ = (-r - m₀) + (-r - m₀) := by omega
          have hr0 : 0 ≤ -r - (m₀ : ℤ) := by
            have : (m₀ : ℤ) ≤ -n := by rwa [hn0] at hle
            omega
          have := hup (-r - (m₀ : ℤ)).toNat
          rw [Int.toNat_of_nonneg hr0] at this
          rw [hn0]
          convert this using 1
          omega
      rcases Int.natAbs_eq n with h | h
      · have hn0 : |n| = n := by rw [← Int.natCast_natAbs]; exact h.symm
        rwa [hn0] at hSabs
      · have hn0 : |n| = -n := by rw [← Int.natCast_natAbs]; omega
        rw [hn0] at hSabs
        have := h2 _ hSabs
        rwa [neg_neg] at this

  have hΛ : ∀ k, Λ k → k = m₀ := by
    intro k hk
    have hk1 := h4a k hk
    obtain ⟨hle, r, hr⟩ := (hS k).mp (hΛS k hk)
    rw [abs_of_pos (by omega)] at hle
    by_contra hne
    have hk2 : (m₀ : ℤ) + 2 ≤ k := by omega
    apply h4b k (by omega) hk
    rw [hS]
    refine ⟨?_, r - 1, by omega⟩
    rw [abs_of_nonneg (by omega)]
    omega
  refine ⟨m₀, by positivity, hS, hΛ, fun h => h4a _ h, fun hnot n => ?_⟩

  have hS2 : S ((m₀ : ℤ) - 2) := by
    by_contra hcon
    exact hnot (h5 _ hm₀ hcon)
  obtain ⟨hle, -⟩ := (hS _).mp hS2
  have hm₀le : m₀ ≤ 1 := by
    by_contra hcon
    rw [abs_of_nonneg (by omega)] at hle
    omega
  rw [hS]
  constructor
  · exact fun h => h.2
  · intro heven
    refine ⟨?_, heven⟩
    interval_cases m₀
    · simp
    ·
      obtain ⟨r, hr⟩ := heven
      rcases le_or_gt 0 n with hn | hn
      · rw [abs_of_nonneg hn]; omega
      · rw [abs_of_neg hn]; omega

end AutomorphicForm.LocalComponentProfileAssembly

open AutomorphicForm.LocalComponentProfileAssembly in
theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (hΘ : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ (fun _ => True))
    (w : InfinitePlace F) (hw : w.IsReal) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module ℂ M) (wt : ℤ → Submodule ℂ M)
      (E L ε : M →ₗ[ℂ] M),
      IsGL2RealKTypeModule wt E L ε ∧ (∀ n : ℤ, FiniteDimensional ℂ (wt n)) ∧
      IsIrreducibleGL2RealKTypeModule wt E L ε ∧ {n : ℤ | wt n ≠ ⊥}.Infinite ∧
      (∀ n : ℤ,
        ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
            (fun φ => HasArchCharacterAt₀ F w
              ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
                (norm_ringEquivRealOfIsReal hw))) φ) ↔
          wt n ≠ ⊥) ∧
      (∀ k : ℤ,
        ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
            (fun φ => HasArchCharacterAt₀ F w
                ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
                  (norm_ringEquivRealOfIsReal hw))) φ ∧
              IsArchLoweringAnnihilatedAt w hw φ) ↔
          ∃ v ∈ wt k, v ≠ 0 ∧ L v = 0) := by

  let S : ℤ → Prop := fun n =>
    ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
      (fun φ => HasArchCharacterAt₀ F w
        ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
          (norm_ringEquivRealOfIsReal hw))) φ)
  let Λ : ℤ → Prop := fun k =>
    ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
      (fun φ => HasArchCharacterAt₀ F w
          ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
            (norm_ringEquivRealOfIsReal hw))) φ ∧
        IsArchLoweringAnnihilatedAt w hw φ)

  have h0 : ∃ n, S n :=
    AutomorphicForm.exists_archOccursInClassOf_archWeightChar_of_coversModCentre
      F c u d₁ d₂ T hd hcov Θ hΘ w hw
  have h1 : ∀ n m, S n → S m → Even (n - m) := fun n m hn hm =>
    AutomorphicForm.even_sub_of_archOccursInClassOf_archWeightChar F _ Θ w hw n m hn hm
  have h2 : ∀ n, S n → S (-n) := fun n hn =>
    AutomorphicForm.archOccursInClassOf_archWeightChar_neg_of_coversModCentre
      F c u d₁ d₂ T hd hcov Θ w hw n hn
  have h3 : ∀ n, 0 ≤ n → S n → S (n + 2) := fun n hn0 hn =>
    AutomorphicForm.archOccursInClassOf_archWeightChar_add_two_of_nonneg_of_coversModCentre
      F c u d₁ d₂ T hd hcov Θ w hw n hn0 hn
  have h4a : ∀ k, Λ k → 1 ≤ k := fun k hk =>
    AutomorphicForm.one_le_of_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_coversModCentre
      F c u d₁ d₂ T hd hcov Θ w hw k hk
  have h4b : ∀ k, 2 ≤ k → Λ k → ¬ S (k - 2) := fun k hk2 hk =>
    AutomorphicForm.not_archOccursInClassOf_archWeightChar_sub_two_of_isArchLoweringAnnihilatedAt_of_coversModCentre
      F c u d₁ d₂ T hd hcov Θ w hw k hk2 hk
  have h5 : ∀ k, S k → ¬ S (k - 2) → Λ k := fun k hk hk2 =>
    AutomorphicForm.archOccursInClassOf_isArchLoweringAnnihilatedAt_of_not_archOccursInClassOf_archWeightChar_sub_two_of_coversModCentre
      F c u d₁ d₂ T hd hcov Θ w hw k hk hk2
  have hΛS : ∀ k, Λ k → S k := fun k hk => ArchOccursInClassOf.and_left hk

  obtain ⟨m₀, hm₀0, hS, hΛ, hΛpos, hpar⟩ := profile S Λ h0 h1 h2 h3 h4a h4b h5 hΛS
  by_cases hlw : Λ m₀
  ·
    obtain ⟨M, i1, i2, wt, E, L, ε, hM, hadm, hirr, hinf, hsupp, hlow⟩ :=
      AutomorphicForm.exists_isIrreducibleGL2RealKTypeModule_lower_eq_zero_iff_of_one_le m₀ (hΛpos hlw)
    refine ⟨M, i1, i2, wt, E, L, ε, hM, hadm, hirr, hinf, fun n => ?_, fun k => ?_⟩
    · exact (hS n).trans (hsupp n).symm
    · refine Iff.trans ?_ (hlow k).symm
      exact ⟨hΛ k, fun h => h ▸ hlw⟩
  ·
    obtain ⟨M, i1, i2, wt, E, L, ε, hM, hadm, hirr, hinf, hsupp, hnolow⟩ :=
      AutomorphicForm.exists_isIrreducibleGL2RealKTypeModule_ne_bot_iff_even_sub m₀
    refine ⟨M, i1, i2, wt, E, L, ε, hM, hadm, hirr, hinf, fun n => ?_, fun k => ?_⟩
    · exact (hpar hlw n).trans (hsupp n).symm
    · constructor
      · intro hk
        exact absurd (hΛ k hk ▸ hk) hlw
      · rintro ⟨v, hv, hv0, hLv⟩
        exact absurd (hnolow k v hv hLv) hv0

end S_AutomorphicForm_exists_isGL2RealKTypeModule_archOccursInClassOf_iff_isArchLoweringAnnihilatedAt_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_exists_isGL2RealKTypeModule_archOccursInClassOf_iff_isArchLoweringAnnihilatedAt_of_coversModCentre (solution)
