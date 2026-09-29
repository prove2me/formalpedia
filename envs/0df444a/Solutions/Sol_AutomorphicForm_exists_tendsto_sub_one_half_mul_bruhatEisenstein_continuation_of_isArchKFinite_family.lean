-- Prove2me | solution 1 for AutomorphicForm.exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/d69ae042-998a-5b4b-af01-adaf5f95bca8

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_ProductionPins
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_StandardGlobalAddChar
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.Convex
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Theorems.Thm_AutomorphicForm_exists_tendsto_tprod_one_sub_absNorm_cpow_mul_weylIntertwiningIntegral_nhds_one_half_of_isArchKFinite_family
import Theorems.Thm_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral
import Theorems.Thm_AutomorphicForm_exists_meromorphicOn_partialEulerProduct_mul_weylIntertwiningIntegral_eq_mul
import Theorems.Thm_AutomorphicForm_exists_unitaryChar_entire_partialEulerProduct_mul_eq_tsum_whittakerCoefficient_bruhatEisenstein
import Theorems.Thm_AutomorphicForm_bruhatEisenstein_eq_constantTerm_add_whittakerSum_of_one_lt_re_of_unitary
import Theorems.Thm_AutomorphicForm_bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family
import Theorems.Thm_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct
import Theorems.Thm_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
import Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
import Theorems.Thm_NumberField_exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero
import Theorems.Thm_NumberField_dedekindZeta_ne_zero_of_one_lt_re
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem"
p2m_attr_erase "instance" "Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul"
p2m_attr_erase "simp" "SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply"
p2m_attr_erase "simp" "RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology
open scoped NNReal

namespace M2aFromLocint

theorem hasProd_of_hasProd_inv {ι : Type*} (f : ι → ℂ) {a : ℂ} (ha : a ≠ 0)
    (h : HasProd (fun i => (f i)⁻¹) a) : HasProd f a⁻¹ := by
  unfold HasProd at h ⊢
  have h' := h.inv₀ ha
  refine h'.congr (fun T => ?_)
  simp [Finset.prod_inv_distrib]

end M2aFromLocint

open M2aFromLocint

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g)),
    ∃ (r : ℂ) (a : ℝ), a < 1 / 2 ∧
      (∀ g : AdelicGL2 (𝓞 F) F, ∃ E' : ℂ → ℂ,
        MeromorphicOn E' Set.univ ∧
        AnalyticOnNhd ℂ E' ({s : ℂ | a < s.re} \ {(1 / 2 : ℂ)}) ∧
        (∀ s : ℂ, 1 / 2 < s.re →
          E' s = φ s g + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F *
            unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
        Tendsto (fun s : ℂ => (s - 1 / 2) * E' s) (𝓝[≠] (1 / 2 : ℂ)) (𝓝 r)) ∧
      ((∀ k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          0 ≤ (φ (1 / 2) k).re ∧ (φ (1 / 2) k).im = 0) →
        (∃ k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) ∧
          φ (1 / 2) k ≠ 0) →
        r ≠ 0) := by
  intro α hα φ hφ hφK hφf hφjc hφhol
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 F) F

  have hφc : ∀ s, Continuous (φ s) := fun s =>
    hφjc.comp (Continuous.prodMk continuous_const continuous_id)
  have hN : ∀ v : HeightOneSpectrum (𝓞 F), (1 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    intro v
    have h1 : 1 < Ideal.absNorm v.asIdeal := by
      rw [Nat.one_lt_iff_ne_zero_and_ne_one]
      exact ⟨by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot,
        by rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top⟩
    exact_mod_cast h1
  have hNC : ∀ v : HeightOneSpectrum (𝓞 F), (((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) ≠ 0 := fun v => by
    exact_mod_cast (lt_trans zero_lt_one (hN v)).ne'
  have h1u : IsUnitaryChar (𝓞 F) F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) := fun x => by simp
  have h1ic : IsIdeleClassChar (𝓞 F) F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) := fun u => by simp
  have hprin : IsPrincipalTrivial (R := 𝓞 F) (K := F) α := by
    intro u
    have h := NumberField.AdeleRing.distribHaarChar_algebraMap F u
    have key : (Units.map (↑(algebraMap F (AdeleRing (𝓞 F) F)) : F →* AdeleRing (𝓞 F) F)) u =
        Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom u := by ext; rfl
    ext
    simp only [α, MonoidHom.coe_toHomUnits, MonoidHom.coe_comp, Function.comp_apply, Units.val_one]
    rw [key, h]
    simp
  set ψ := NumberField.StandardAddChar.stdAddChar F with hψdef
  have hψ : IsGlobalAddChar F ψ := NumberField.StandardAddChar.isGlobalAddChar_stdAddChar F
  have hO0 : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hO1 : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hhalf : (𝓝[{s : ℂ | 1 / 2 < s.re}] (1 / 2 : ℂ)).NeBot := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    rw [Complex.closure_setOf_lt_re]
    show (1 / 2 : ℝ) ≤ (1 / 2 : ℂ).re
    norm_num
  have h2an : ∀ x : ℂ, AnalyticAt ℂ (fun s : ℂ => 2 * s) x := fun x => analyticAt_const.mul analyticAt_id
  have h21an : ∀ x : ℂ, AnalyticAt ℂ (fun s : ℂ => 2 * s + 1) x := fun x =>
    (h2an x).add analyticAt_const

  set cV : ℂ := ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℝ) : ℂ) with hcV_def
  have hcV : cV ≠ 0 := by
    rw [hcV_def, Complex.ofReal_ne_zero]
    exact (ENNReal.toReal_pos (adelicAddHaar_adelicBox_pos F).ne' (adelicAddHaar_adelicBox_lt_top F).ne).ne'

  let FS : Finset (HeightOneSpectrum (𝓞 F)) → ℂ → ℂ := fun S w =>
    ∏ v ∈ S, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))
  have hFSdiff : ∀ S, Differentiable ℂ (FS S) := by
    intro S w
    show DifferentiableAt ℂ (fun w : ℂ => ∏ v ∈ S, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))) w
    refine DifferentiableAt.fun_finsetProd (fun v _ => ?_)
    exact (differentiableAt_const _).sub (differentiableAt_id.neg.const_cpow (Or.inl (hNC v)))
  have hFSan : ∀ S (x : ℂ), AnalyticAt ℂ (FS S) x := fun S x => (hFSdiff S).analyticAt x
  have hFSne : ∀ S (w : ℂ), 0 < w.re → FS S w ≠ 0 := by
    intro S w hw
    show (∏ v ∈ S, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))) ≠ 0
    refine Finset.prod_ne_zero_iff.mpr (fun v _ => ?_)
    have hpos : 0 < Ideal.absNorm v.asIdeal := by exact_mod_cast (lt_trans zero_lt_one (hN v))
    have hlt : ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg (hN v) (by linarith)
    intro h
    rw [sub_eq_zero] at h
    rw [← h, norm_one] at hlt
    exact lt_irrefl _ hlt

  obtain ⟨Rζ, hRζd, hRζ1, hRζeq, -⟩ :=
    NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero F
  have hRζan : ∀ x : ℂ, AnalyticAt ℂ Rζ x := fun x => hRζd.analyticAt x
  let ζc : ℂ → ℂ := fun w => Rζ w / (w - 1)
  have hζc_eq : ∀ w : ℂ, 1 < w.re → ζc w = NumberField.dedekindZeta F w := by
    intro w hw
    have hw1 : w - 1 ≠ 0 := by
      intro h; rw [sub_eq_zero] at h; rw [h] at hw; norm_num at hw
    simp only [ζc, hRζeq w hw]
    field_simp
  have hζcan : ∀ w : ℂ, w ≠ 1 → AnalyticAt ℂ ζc w := fun w hw =>
    (hRζan w).div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hw)
  have hζcne : ∀ w : ℂ, 1 < w.re → ζc w ≠ 0 := fun w hw => by
    rw [hζc_eq w hw]; exact NumberField.dedekindZeta_ne_zero_of_one_lt_re F hw

  have hpartial : ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (w : ℂ), 1 < w.re →
      NumberField.dedekindZeta F w * FS S w ≠ 0 ∧
      (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
          (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))) = (NumberField.dedekindZeta F w * FS S w)⁻¹ := by
    intro S w hw
    have hFSw : FS S w ≠ 0 := hFSne S w (by linarith)
    have hFSw' : (∏ v ∈ S, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))) ≠ 0 := hFSw
    have hζ : NumberField.dedekindZeta F w ≠ 0 := NumberField.dedekindZeta_ne_zero_of_one_lt_re F hw
    have hne : NumberField.dedekindZeta F w * FS S w ≠ 0 := mul_ne_zero hζ hFSw
    refine ⟨hne, ?_⟩
    have hall := NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta F w hw
    set f : HeightOneSpectrum (𝓞 F) → ℂ := fun v => (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))⁻¹
      with hf_def
    obtain ⟨hmul1, -, -⟩ := NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
      F S (fun _ => 1) (fun _ => by simp)
    have hm : Multipliable (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => f v.1) := by
      simpa only [hf_def, one_mul] using hmul1 w hw
    have hb : HasProd (f ∘ (↑) : ((↑S : Set (HeightOneSpectrum (𝓞 F)))ᶜ : Set _) → ℂ)
        (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, f v.1) := hm.hasProd
    have hS := Finset.hasProd S f
    have hfull := hS.mul_compl hb
    have hall' : HasProd f (NumberField.dedekindZeta F w) := hall
    have huniq := hall'.unique hfull
    have hprodS : ∏ b ∈ S, f b = (FS S w)⁻¹ := by
      simp only [hf_def, Finset.prod_inv_distrib]
      rfl
    have hval : (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, f v.1) =
        NumberField.dedekindZeta F w * FS S w := by
      rw [hprodS] at huniq
      field_simp at huniq
      exact huniq.symm
    have hcompl : HasProd (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
        (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))⁻¹)
        (NumberField.dedekindZeta F w * FS S w) := by
      rw [← hval]; exact hm.hasProd
    exact (hasProd_of_hasProd_inv _ hne hcompl).tprod_eq

  obtain ⟨S₀, hS₀⟩ :=
    AutomorphicForm.exists_tendsto_tprod_one_sub_absNorm_cpow_mul_weylIntertwiningIntegral_nhds_one_half_of_isArchKFinite_family
      F hα φ hφ hφK hφf hφjc hφhol
  obtain ⟨ρ, hρlim, hρne⟩ := hS₀ S₀ subset_rfl

  refine ⟨cV⁻¹ * (Rζ 1 / 2) * FS S₀ 1 * ρ, 1 / 4, by norm_num, ?_, ?_⟩
  swap
  · intro hpos hex
    have h1 : FS S₀ 1 ≠ 0 := hFSne S₀ 1 (by norm_num)
    have h2 : (Rζ 1 / 2) ≠ 0 := div_ne_zero hRζ1 two_ne_zero
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero hcV) h2) h1) (hρne hpos hex)
  intro g

  obtain ⟨T, ϖ₁, hϖ₁, R, hRmero, hRdiff, hRid⟩ :=
    AutomorphicForm.exists_meromorphicOn_partialEulerProduct_mul_weylIntertwiningIntegral_eq_mul
      F hα 1 1 h1u h1u φ hφ hφK hφf hφjc hφhol g
  have hloc : ∀ (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ),
      ((NumberField.TateGlobal.localChar (1 * 1⁻¹ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) v u : ℂˣ) : ℂ) = 1 := by
    intro v u
    simp [NumberField.TateGlobal.localChar]
  simp only [hloc, one_mul] at hRid
  have hRan : ∀ x : ℂ, 0 < x.re → AnalyticAt ℂ R x := fun x hx => hRdiff.analyticAt (hO0.mem_nhds hx)

  obtain ⟨χ, hχc, hχu, hχic, S₇, ϖ₇, hϖ₇, Nc, hNcd, hNcid⟩ :=
    AutomorphicForm.exists_unitaryChar_entire_partialEulerProduct_mul_eq_tsum_whittakerCoefficient_bruhatEisenstein
      F hα hprin 1 1 h1u h1u h1ic h1ic ψ hψ φ hφ hφK hφf hφjc hφhol g
  obtain ⟨Lχ, hLmero, hLid⟩ :=
    NumberField.TateGlobal.exists_meromorphicOn_eq_partialEulerProduct F S₇ ϖ₇ hϖ₇ χ hχc hχu hχic
  have hzχ : ∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S₇},
      ‖((NumberField.TateGlobal.localChar χ v.1 (ϖ₇ v.1) : ℂˣ) : ℂ)‖ ≤ 1 := fun v => (hχu _).le
  obtain ⟨hmulχ, hdiffχ, hneχ⟩ :=
    NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one F S₇
      (fun v => ((NumberField.TateGlobal.localChar χ v.1 (ϖ₇ v.1) : ℂˣ) : ℂ)) hzχ
  have hLEL : ∀ w : ℂ, 1 < w.re → Lχ w =
      ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S₇},
        (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ₇ v.1) : ℂˣ) : ℂ) *
          ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))⁻¹ := by
    intro w hw
    rw [hLid w hw]
    have h := hasProd_of_hasProd_inv
      (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S₇} =>
        (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ₇ v.1) : ℂˣ) : ℂ) *
          ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))) (hneχ w hw) (hmulχ w hw).hasProd
    rw [h.tprod_eq, inv_inv]
  have hLan : ∀ w : ℂ, 1 < w.re → AnalyticAt ℂ Lχ w ∧ Lχ w ≠ 0 := by
    intro w hw
    have hmem : {s : ℂ | 1 < s.re} ∈ 𝓝 w := hO1.mem_nhds hw
    have hELan := hdiffχ.analyticAt hmem
    have heq : Lχ =ᶠ[𝓝 w] (fun s : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S₇},
        (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ₇ v.1) : ℂˣ) : ℂ) *
          ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) :=
      Filter.eventuallyEq_of_mem hmem (fun s hs => hLEL s hs)
    exact ⟨hELan.congr heq.symm, by rw [hLEL w hw]; exact hneχ w hw⟩

  let ZT : ℂ → ℂ := fun w => ζc w * FS T w
  let Mc : ℂ → ℂ := fun s => R s * ZT (2 * s) / ZT (2 * s + 1)
  let NC : ℂ → ℂ := fun s => Nc s * (Lχ (2 * s + 1))⁻¹
  let E' : ℂ → ℂ := fun s => φ s g + cV⁻¹ * Mc s + NC s
  have hZTan : ∀ w : ℂ, w ≠ 1 → AnalyticAt ℂ ZT w := fun w hw => (hζcan w hw).mul (hFSan T w)
  have hZTne : ∀ w : ℂ, 1 < w.re → ZT w ≠ 0 := fun w hw =>
    mul_ne_zero (hζcne w hw) (hFSne T w (by linarith))

  have hNCan : ∀ x : ℂ, 0 < x.re → AnalyticAt ℂ NC x := by
    intro x hx
    have hre21 : 1 < (2 * x + 1).re := by simp; linarith
    have hL21 : AnalyticAt ℂ (fun s => Lχ (2 * s + 1)) x := (hLan _ hre21).1.comp_of_eq (h21an x) rfl
    exact (hNcd.analyticAt x).mul (hL21.inv (hLan _ hre21).2)
  have hZT21an : ∀ x : ℂ, 0 < x.re → AnalyticAt ℂ (fun s => ZT (2 * s + 1)) x ∧ ZT (2 * x + 1) ≠ 0 := by
    intro x hx
    have h2x11 : (2 * x + 1) ≠ 1 := by
      intro h
      have : x = 0 := by linear_combination h / 2
      rw [this] at hx; simp at hx
    have hre21 : 1 < (2 * x + 1).re := by simp; linarith
    exact ⟨(hZTan _ h2x11).comp_of_eq (h21an x) rfl, hZTne _ hre21⟩
  have hMcan : ∀ x : ℂ, 0 < x.re → x ≠ 1 / 2 → AnalyticAt ℂ Mc x := by
    intro x hx hx12
    have h2x1 : (2 * x) ≠ 1 := by
      intro h; apply hx12; linear_combination h / 2
    have hZT2 : AnalyticAt ℂ (fun s => ZT (2 * s)) x := (hZTan _ h2x1).comp_of_eq (h2an x) rfl
    exact ((hRan x hx).mul hZT2).div (hZT21an x hx).1 (hZT21an x hx).2
  have hE'an : ∀ x : ℂ, 0 < x.re → x ≠ 1 / 2 → AnalyticAt ℂ E' x := by
    intro x hx hx12
    exact (((hφhol g).analyticAt x).add (analyticAt_const.mul (hMcan x hx hx12))).add (hNCan x hx)

  have hMc : ∀ s : ℂ, 1 / 2 < s.re →
      weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g = Mc s := by
    intro s hs
    have h2s : 1 < (2 * s).re := by simp; linarith
    have h2s1 : 1 < (2 * s + 1).re := by simp; linarith
    obtain ⟨hA, hP2s⟩ := hpartial T (2 * s) h2s
    obtain ⟨hB, hP2s1⟩ := hpartial T (2 * s + 1) h2s1
    have hid := hRid s hs
    rw [hP2s, hP2s1] at hid
    have hM : weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g =
        (NumberField.dedekindZeta F (2 * s) * FS T (2 * s)) *
          ((NumberField.dedekindZeta F (2 * s + 1) * FS T (2 * s + 1))⁻¹ * R s) := by
      rw [← hid, ← mul_assoc, mul_inv_cancel₀ hA, one_mul]
    rw [hM]
    simp only [Mc, ZT, hζc_eq _ h2s, hζc_eq _ h2s1]
    field_simp

  have hNCeq : ∀ s : ℂ, 1 < s.re → NC s =
      ∑' ξ : {ξ : F // ξ ≠ 0},
        whittakerCoefficient F (productionPins F) ψ
          (fun g' => φ s g' + ∑' ξ' : F, φ s (adelicWeyl (𝓞 F) F
              * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g')) (ξ : F) g := by
    intro s hs
    have h2s1 : 1 < (2 * s + 1).re := by simp; linarith
    rw [← hNcid s hs]
    simp only [NC]
    rw [hLid (2 * s + 1) h2s1, inv_inv, mul_comm]

  have hagree1 : ∀ s : ℂ, 1 < s.re →
      E' s = φ s g + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g) := by
    intro s hs
    have hs' : 1 / 2 < s.re := by linarith
    have hF := AutomorphicForm.bruhatEisenstein_eq_constantTerm_add_whittakerSum_of_one_lt_re_of_unitary
      F hα 1 1 h1u h1u ψ hψ φ hφ hφK hφf hφc g s hs
    have hCT := AutomorphicForm.constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral
      F hα 1 1 h1u h1u s hs' (φ s) (hφ s) (hφc s) g
    dsimp only at hCT
    have key : φ s g + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g) =
        (φ s g + cV⁻¹ * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g) +
        ∑' ξ : {ξ : F // ξ ≠ 0},
          whittakerCoefficient F (productionPins F) ψ
            (fun g' => φ s g' + ∑' ξ' : F, φ s (adelicWeyl (𝓞 F) F
                * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g')) (ξ : F) g := by
      rw [hF]
      congr 1
    rw [key, hMc s hs', ← hNCeq s hs]

  refine ⟨E', ?mero, ?anal, ?agree, ?tend⟩
  case mero =>
    intro x _
    have hφm : MeromorphicAt (fun s => φ s g) x := ((hφhol g).analyticAt x).meromorphicAt
    have hζcm : ∀ y : ℂ, MeromorphicAt ζc y := fun y =>
      (hRζan y).meromorphicAt.div ((analyticAt_id.sub analyticAt_const).meromorphicAt)
    have hZTm : ∀ y : ℂ, MeromorphicAt ZT y := fun y => (hζcm y).mul (hFSan T y).meromorphicAt
    have hZT2 : MeromorphicAt (fun s => ZT (2 * s)) x :=
      MeromorphicAt.comp_analyticAt (g := fun s : ℂ => 2 * s) (hZTm _) (h2an x)
    have hZT21 : MeromorphicAt (fun s => ZT (2 * s + 1)) x :=
      MeromorphicAt.comp_analyticAt (g := fun s : ℂ => 2 * s + 1) (hZTm _) (h21an x)
    have hMcm : MeromorphicAt Mc x := ((hRmero x (Set.mem_univ x)).mul hZT2).div hZT21
    have hL21 : MeromorphicAt (fun s => Lχ (2 * s + 1)) x :=
      MeromorphicAt.comp_analyticAt (g := fun s : ℂ => 2 * s + 1) (hLmero _ (Set.mem_univ _)) (h21an x)
    have hNCm : MeromorphicAt NC x := (hNcd.analyticAt x).meromorphicAt.mul hL21.inv
    exact (hφm.add ((MeromorphicAt.const _ x).mul hMcm)).add hNCm
  case anal =>
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx1' : 1 / 4 < x.re := hx1
    refine hE'an x (by linarith) ?_
    intro h
    exact hx2 (by rw [h]; exact Set.mem_singleton _)
  case agree =>
    intro s hs
    have hBan : AnalyticOnNhd ℂ (fun s : ℂ => φ s g + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) {s : ℂ | 1 / 2 < s.re} :=
      (AutomorphicForm.bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family
        F hα 1 1 h1u h1u φ hφ hφjc hφhol g).analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)
    have hE'U : AnalyticOnNhd ℂ E' {s : ℂ | 1 / 2 < s.re} := by
      intro x hx
      have hx' : 1 / 2 < x.re := hx
      refine hE'an x (by linarith) ?_
      intro h; rw [h] at hx'; norm_num at hx'
    have hpre : IsPreconnected {s : ℂ | 1 / 2 < s.re} := (convex_halfSpace_re_gt (1 / 2)).isPreconnected
    have h2mem : (2 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by
      show (1 / 2 : ℝ) < (2 : ℂ).re; norm_num
    have hev : E' =ᶠ[𝓝 (2 : ℂ)] (fun s : ℂ => φ s g + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) := by
      have hmem : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
        hO1.mem_nhds (by show (1 : ℝ) < (2 : ℂ).re; norm_num)
      exact Filter.eventuallyEq_of_mem hmem (fun s hs => hagree1 s hs)
    exact hE'U.eqOn_of_preconnected_of_eventuallyEq hBan hpre h2mem hev hs
  case tend =>

    let H : ℂ → ℂ := fun s => (s - 1 / 2) * φ s g +
      cV⁻¹ * (R s * (Rζ (2 * s) * FS T (2 * s) / 2) / ZT (2 * s + 1)) + (s - 1 / 2) * NC s
    have hkey : ∀ s : ℂ, s ≠ 1 / 2 → (s - 1 / 2) * ZT (2 * s) = Rζ (2 * s) * FS T (2 * s) / 2 := by
      intro s hs
      have h2s1 : (2 * s - 1) ≠ 0 := by
        intro h; apply hs; linear_combination h / 2
      have e : (s - 1 / 2) / (2 * s - 1) = 1 / 2 := (div_eq_iff h2s1).mpr (by ring)
      simp only [ZT, ζc]
      calc (s - 1 / 2) * (Rζ (2 * s) / (2 * s - 1) * FS T (2 * s))
          = ((s - 1 / 2) / (2 * s - 1)) * (Rζ (2 * s) * FS T (2 * s)) := by ring
        _ = Rζ (2 * s) * FS T (2 * s) / 2 := by rw [e]; ring
    have hHeq : ∀ s : ℂ, s ≠ 1 / 2 → H s = (s - 1 / 2) * E' s := by
      intro s hs
      have : (s - 1 / 2) * E' s = (s - 1 / 2) * φ s g +
          cV⁻¹ * (R s * ((s - 1 / 2) * ZT (2 * s)) / ZT (2 * s + 1)) + (s - 1 / 2) * NC s := by
        simp only [E', Mc]; ring
      rw [this, hkey s hs]

    have hx : (0 : ℝ) < (1 / 2 : ℂ).re := by norm_num
    have hsub : AnalyticAt ℂ (fun s : ℂ => s - 1 / 2) (1 / 2) := analyticAt_id.sub analyticAt_const
    have hRζ2 : AnalyticAt ℂ (fun s : ℂ => Rζ (2 * s)) (1 / 2) := (hRζan _).comp_of_eq (h2an _) rfl
    have hFS2 : AnalyticAt ℂ (fun s : ℂ => FS T (2 * s)) (1 / 2) := (hFSan T _).comp_of_eq (h2an _) rfl
    have hHan : AnalyticAt ℂ H (1 / 2) :=
      ((hsub.mul ((hφhol g).analyticAt _)).add (analyticAt_const.mul
        (((hRan _ hx).mul ((hRζ2.mul hFS2).div analyticAt_const two_ne_zero)).div
          (hZT21an _ hx).1 (hZT21an _ hx).2))).add (hsub.mul (hNCan _ hx))
    have hT1 : Tendsto H (𝓝[≠] (1 / 2 : ℂ)) (𝓝 (H (1 / 2))) :=
      hHan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hT2 : Tendsto (fun s : ℂ => (s - 1 / 2) * E' s) (𝓝[≠] (1 / 2 : ℂ)) (𝓝 (H (1 / 2))) :=
      hT1.congr' (eventually_nhdsWithin_of_forall (fun s hs => hHeq s hs))

    let J : ℂ → ℂ := fun s => R s * FS T (2 * s) / (FS S₀ (2 * s) * ZT (2 * s + 1))
    have hJeq : ∀ s : ℂ, 1 / 2 < s.re →
        J s = (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S₀},
            (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))) *
          weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g := by
      intro s hs
      have h2s : 1 < (2 * s).re := by simp; linarith
      have h2s1 : 1 < (2 * s + 1).re := by simp; linarith
      obtain ⟨hA, hP⟩ := hpartial S₀ (2 * s) h2s
      have hz : NumberField.dedekindZeta F (2 * s) ≠ 0 := NumberField.dedekindZeta_ne_zero_of_one_lt_re F h2s
      have hf0 : FS S₀ (2 * s) ≠ 0 := hFSne S₀ _ (by linarith)
      have hf1 : FS T (2 * s + 1) ≠ 0 := hFSne T _ (by linarith)
      have hf2 : FS T (2 * s) ≠ 0 := hFSne T _ (by linarith)
      have hzc : ζc (2 * s + 1) ≠ 0 := hζcne _ h2s1
      rw [hP, hMc s hs]
      simp only [J, Mc, ZT, hζc_eq _ h2s]
      field_simp
    have hFS01 : AnalyticAt ℂ (fun s : ℂ => FS S₀ (2 * s)) (1 / 2) := (hFSan S₀ _).comp_of_eq (h2an _) rfl
    have hFS01ne : FS S₀ (2 * (1 / 2 : ℂ)) ≠ 0 := hFSne S₀ _ (by norm_num)
    have hJan : AnalyticAt ℂ J (1 / 2) :=
      ((hRan _ hx).mul hFS2).div (hFS01.mul (hZT21an _ hx).1) (mul_ne_zero hFS01ne (hZT21an _ hx).2)
    have hT3 : Tendsto J (𝓝[{s : ℂ | 1 / 2 < s.re}] (1 / 2 : ℂ)) (𝓝 (J (1 / 2))) :=
      hJan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hT4 : Tendsto (fun s : ℂ => (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S₀},
            (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))) *
          weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g)
        (𝓝[{s : ℂ | 1 / 2 < s.re}] (1 / 2 : ℂ)) (𝓝 (J (1 / 2))) :=
      hT3.congr' (eventually_nhdsWithin_of_forall (fun s hs => hJeq s hs))
    have hρJ : ρ = J (1 / 2) := tendsto_nhds_unique (hρlim g) hT4

    have hZT2ne : ZT (2 * (1 / 2 : ℂ) + 1) ≠ 0 := (hZT21an _ hx).2
    have hHval : H (1 / 2) = cV⁻¹ * (Rζ 1 / 2) * FS S₀ 1 * ρ := by
      rw [hρJ]
      simp only [H, J, sub_self, zero_mul, zero_add, add_zero]
      have e1 : (2 : ℂ) * (1 / 2) = 1 := by norm_num
      rw [e1] at hFS01ne hZT2ne ⊢
      field_simp
    rw [← hHval]
    exact hT2

end S_AutomorphicForm_exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family
end P2MW
export P2MW.S_AutomorphicForm_exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family (solution)
