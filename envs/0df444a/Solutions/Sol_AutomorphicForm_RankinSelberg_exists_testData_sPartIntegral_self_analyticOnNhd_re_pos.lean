-- Prove2me | solution 1 for AutomorphicForm.RankinSelberg.exists_testData_sPartIntegral_self_analyticOnNhd_re_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/5d6ac440-48b5-5c86-b828-57688a952864

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_AutomorphicForm_RankinSelbergQuotientIntegral
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Theorems.Thm_AutomorphicForm_exists_isUnitFactorizableAboveOfType_biInvariant_rightConv_ne_zero_of_mem_archCutSubmodule
import Theorems.Thm_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType
import Theorems.Thm_AutomorphicForm_isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow
import Theorems.Thm_AutomorphicForm_exists_flat_isInducedSection_family_eq_of_isInducedSection
import Theorems.Thm_AutomorphicForm_IsInducedSection_eq_of_eqOn_maximalCompact
import Theorems.Thm_AutomorphicForm_exists_measurableSet_isFundamentalDomain_subset_iUnion_integralWindowedSiegelSet_of_coversModCentre
import Theorems.Thm_AutomorphicForm_exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre
import Theorems.Thm_AutomorphicForm_peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous
import Theorems.Thm_UnramifiedWhittaker_mul_conj_apply_heckeGen_pow_mul_eq_of_shell_zero
import Theorems.Thm_AutomorphicForm_heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps
import Theorems.Thm_AutomorphicForm_integrableOn_norm_rightConv_sq_mul_archHeight_pow_mul_ideleNorm_rpow_inter_centreCutSiegelSet
import Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_count_differentIdeal
import Theorems.Thm_AutomorphicForm_exists_unipotent_surgery_whittakerCoefficient_diagOne_mul_eq_sum_mul
import Theorems.Thm_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_AutomorphicForm_exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection
import Theorems.Thm_AutomorphicForm_exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet
import Theorems.Thm_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
import Theorems.Thm_AutomorphicForm_exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Theorems.Thm_AutomorphicForm_exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc
import Theorems.Thm_AutomorphicForm_summable_norm_whittakerCoefficient_of_isKfSmooth_of_contDiff_mixedSpace
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
import Theorems.Thm_AutomorphicForm_exists_lintegral_rationalCentreUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa
import Theorems.Thm_NumberField_Idele_exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const
import Theorems.Thm_AutomorphicForm_exists_unipotent_surgery_whittakerCoefficient_diagOne_mul_eq_sum_mul_shell
import Theorems.Thm_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero
import Theorems.Thm_AutomorphicForm_exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero
import Theorems.Thm_AutomorphicForm_hasSum_whittakerCoefficient_one_diagOne_principalIdeles_mul
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_of_isCuspConstituent
import Theorems.Thm_AutomorphicForm_exists_whittakerCoefficient_one_diagOne_eq_zero_of_exp_lt_valuation
import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_unramified_package_rightConv_sum_translate
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_mem_maximalCompactAt_whittakerCoefficient_rightConv_diagOne_mul_ne_zero
import Theorems.Thm_AutomorphicForm_RankinSelberg_analyticOnNhd_sPartIntegral_and_pos_of_shell_surgery
import Theorems.Thm_AutomorphicForm_apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway
import Theorems.Thm_AutomorphicForm_exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_norm_whittakerCoefficient_diagOne_mul_le_ideleNorm_rpow_mul_prod_min_of_isCuspConstituent_mul_of_glArch_eq_one
import Theorems.Thm_AutomorphicForm_exists_norm_whittakerCoefficient_rightConv_diagOne_mul_le_ideleNorm_rpow_mul_norm_infinitePlace_rpow_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_RankinSelberg_exists_testData_sPartIntegral_self_analyticOnNhd_re_pos
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec"
set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
p2m_open "AutomorphicForm~det_centralScalar AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp IsDedekindDomain"
open AutomorphicForm.CuspidalConstituent
open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

open AutomorphicForm.CuspidalConstituent HeckeIntegralSeam NumberField.AdelicHeight
open scoped Classical nonZeroDivisors

section
open LocalGL2 AdelicDock NumberField.AdelicLevel

namespace RS12L

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem diagZ_one_eq_diagPi (ϖ : v.adicCompletionIntegers K)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0) :
    UnramifiedWhittaker.diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hϖ0 1 =
      diagPi ϖ hϖ0 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [UnramifiedWhittaker.diagZ, coe_diagPi]

theorem repSome_eq_localRepSome (ϖ : v.adicCompletionIntegers K)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0) (b : v.adicCompletionIntegers K) :
    UnramifiedWhittaker.repSome (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hϖ0
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) b) = localRepSome ϖ hϖ0 b := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [UnramifiedWhittaker.repSome, localRepSome, Matrix.mul_apply, Fin.sum_univ_two]

theorem repInf_eq_localRepInf (ϖ : v.adicCompletionIntegers K)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0) :
    UnramifiedWhittaker.repInf (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hϖ0 =
      localRepInf (K := v.adicCompletion K) ϖ hϖ0 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [UnramifiedWhittaker.repInf, localRepInf, Matrix.mul_apply, Fin.sum_univ_two]

theorem placeEmbed_unipotent (xv : v.adicCompletion K) :
    UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.unipotent xv) =
      unipotentGL2 (R := AdeleRing (𝓞 K) K) (NumberField.StandardAddChar.adeleSingleAt K v xv) := by
  have h1 : UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.unipotent xv) =
      finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v (UnramifiedWhittaker.unipotent xv)) := rfl
  rw [h1]
  refine Units.ext ?_
  rw [coe_finEmbed, coe_localEmbed, unipotentGL2_coe]
  refine matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 K) K ?_ ?_
  · rw [mapMatrix_arch_finMat]
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch_apply, NumberField.StandardAddChar.adeleSingleAt_apply]
    fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, Prod.fst_one, Prod.fst_zero] <;> rfl
  · rw [mapMatrix_fin_finMat]
    refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 K) K fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [mapMatrix_localMat_self]
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleFin_apply, finAdeleEval_apply,
        NumberField.StandardAddChar.adeleSingleAt_apply]
      fin_cases i <;> fin_cases j <;>
        simp [UnramifiedWhittaker.unipotent, Matrix.one_apply, Prod.snd_one, Prod.snd_zero,
          NumberField.StandardAddChar.finAdeleSingleAt_apply_self] <;> rfl
    · rw [mapMatrix_localMat_of_ne (𝓞 K) K v _ hw]
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleFin_apply, finAdeleEval_apply,
        NumberField.StandardAddChar.adeleSingleAt_apply]
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.one_apply, Prod.snd_one, Prod.snd_zero,
          NumberField.StandardAddChar.finAdeleSingleAt_apply_of_ne K v xv hw] <;> rfl

end RS12L

end

namespace RS12W

variable (F : Type) [Field F] [NumberField F] (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)

theorem whittakerCoefficient_mul_right (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g k : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ α (g * k) = whittakerCoefficient F pins ψ (fun y => φ (y * k)) α g := by
  letI := pins.nS
  simp only [whittakerCoefficient, mul_assoc]

theorem whittakerCoefficient_mul_right_eq_of_forall (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g k : AdelicGL2 (𝓞 F) F)
    (hk : ∀ y, φ (y * k) = φ y) :
    whittakerCoefficient F pins ψ φ α (g * k) = whittakerCoefficient F pins ψ φ α g := by
  rw [whittakerCoefficient_mul_right]
  congr 1
  funext y
  exact hk y

theorem whittakerCoefficient_mul_central (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g c : AdelicGL2 (𝓞 F) F) (ω : ℂ)
    (hcomm : ∀ h : AdelicGL2 (𝓞 F) F, h * c = c * h) (hc : ∀ h, φ (c * h) = ω * φ h) :
    whittakerCoefficient F pins ψ φ α (g * c) = ω * whittakerCoefficient F pins ψ φ α g := by
  letI := pins.nS
  simp only [whittakerCoefficient]
  rw [← integral_const_mul]
  congr 1
  funext u
  rw [← mul_assoc, hcomm (unipotentGL2 u * g), hc]
  ring

theorem sum_whittakerCoefficient_mul_right_eq {ι : Type*} [Fintype ι] (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F)
    (g : AdelicGL2 (𝓞 F) F) (r : ι → AdelicGL2 (𝓞 F) F) (a : ℂ)
    (hsum : ∀ h : AdelicGL2 (𝓞 F) F, (∑ j, φ (h * r j)) = a * φ h)
    (hint : ∀ j, WhittakerCoefficientIntegrable F pins ψ (fun y => φ (y * r j)) α g) :
    (∑ j, whittakerCoefficient F pins ψ φ α (g * r j)) = a * whittakerCoefficient F pins ψ φ α g := by
  letI := pins.nS
  simp only [whittakerCoefficient_mul_right]
  simp only [whittakerCoefficient]
  rw [← integral_finset_sum _ (fun j _ => hint j), ← integral_const_mul]
  congr 1
  funext u
  rw [← Finset.sum_mul, hsum]
  ring

end RS12W

namespace RS12L_e13

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

noncomputable def zIdele (π : v.adicCompletion K) (hπ : π ≠ 0) : (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (Units.mk0 π hπ))

theorem zIdele_fst (π : v.adicCompletion K) (hπ : π ≠ 0) : ((zIdele K v π hπ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := rfl

theorem zIdele_snd_self (π : v.adicCompletion K) (hπ : π ≠ 0) :
    ((zIdele K v π hπ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = π := by
  change ((localUnit (𝓞 K) K v (Units.mk0 π hπ) : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v = π
  rw [localUnit_apply_self]; rfl

theorem zIdele_snd_of_ne (π : v.adicCompletion K) (hπ : π ≠ 0) {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v) :
    ((zIdele K v π hπ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w = 1 := by
  change ((localUnit (𝓞 K) K v (Units.mk0 π hπ) : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w = 1
  exact localUnit_apply_of_ne _ _ _ _ hw

private theorem adele_ext {a b : AdeleRing (𝓞 K) K} (h1 : ∀ w, a.1 w = b.1 w) (h2 : ∀ u, a.2 u = b.2 u) : a = b :=
  Prod.ext (funext h1) (RestrictedProduct.ext _ _ h2)

theorem placeEmbed_scalarPi (π : v.adicCompletion K) (hπ : π ≠ 0) :
    UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.scalarPi π hπ) = centralScalar (𝓞 K) K (zIdele K v π hπ) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have lhs : ((UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.scalarPi π hπ) : AdelicGL2 (𝓞 K) K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      AdelicDock.finMat (𝓞 K) K (AdelicDock.localMat (𝓞 K) K v
        ((UnramifiedWhittaker.scalarPi π hπ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) i j := rfl
  have hsc : ((UnramifiedWhittaker.scalarPi π hπ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![π, 0; 0, π] := rfl
  have rhs : ((centralScalar (𝓞 K) K (zIdele K v π hπ) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      (Matrix.scalar (Fin 2) ((zIdele K v π hπ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) i j := rfl
  rw [lhs, hsc, rhs, Matrix.scalar_apply, Matrix.diagonal_apply]
  refine adele_ext K (fun w => ?_) (fun u => ?_)
  · change (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j w = _
    rw [Matrix.one_apply]
    split_ifs <;> rfl
  · change AdelicDock.splice (𝓞 K) K v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j)
        ((!![π, 0; 0, π] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) u = _
    by_cases hu : u = v
    · subst hu
      rw [AdelicDock.splice_apply_self]
      split_ifs with hij
      · subst hij; rw [zIdele_snd_self]; fin_cases i <;> rfl
      · fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | rfl
    · rw [AdelicDock.splice_apply_of_ne _ _ _ _ _ hu, Matrix.one_apply]
      split_ifs with hij
      · rw [zIdele_snd_of_ne K v π hπ hu]; rfl
      · rfl

theorem det_placeEmbed_diagZ_one (π : v.adicCompletion K) (hπ : π ≠ 0) :
    Matrix.GeneralLinearGroup.det (UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.diagZ π hπ 1)) = zIdele K v π hπ := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change (AdelicDock.finMat (𝓞 K) K (AdelicDock.localMat (𝓞 K) K v (!![π ^ (1 : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))).det = _
  set D : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) := !![π ^ (1 : ℤ), 0; 0, 1] with hD
  set M := AdelicDock.finMat (𝓞 K) K (AdelicDock.localMat (𝓞 K) K v D) with hM
  refine Prod.ext ?_ (RestrictedProduct.ext _ _ fun u => ?_)
  ·
    have h := RingHom.map_det (adeleArch (𝓞 K) K) M
    rw [hM, AdelicDock.mapMatrix_arch_finMat, Matrix.det_one] at h
    exact h
  ·
    have h := RingHom.map_det ((finAdeleEval (𝓞 K) K u).comp (adeleFin (𝓞 K) K)) M
    have e : ((finAdeleEval (𝓞 K) K u).comp (adeleFin (𝓞 K) K)).mapMatrix M =
        (finAdeleEval (𝓞 K) K u).mapMatrix ((adeleFin (𝓞 K) K).mapMatrix M) := by
      rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, RingHom.coe_comp, Matrix.map_map]
    rw [e, hM, AdelicDock.mapMatrix_fin_finMat] at h
    change ((finAdeleEval (𝓞 K) K u).comp (adeleFin (𝓞 K) K)) M.det = _
    rw [h]
    by_cases hu : u = v
    · subst hu
      rw [AdelicDock.mapMatrix_localMat_self]
      have hdet : D.det = π := by rw [hD, Matrix.det_fin_two_of]; simp
      exact hdet.trans (zIdele_snd_self K u π hπ).symm
    · rw [AdelicDock.mapMatrix_localMat_of_ne _ _ _ _ hu, Matrix.det_one]
      exact (zIdele_snd_of_ne K v π hπ hu).symm

theorem centralScalar_comm (z : (AdeleRing (𝓞 K) K)ˣ) (h : AdelicGL2 (𝓞 K) K) :
    h * centralScalar (𝓞 K) K z = centralScalar (𝓞 K) K z * h := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  change (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * Matrix.scalar (Fin 2) ((z : AdeleRing (𝓞 K) K)) =
    Matrix.scalar (Fin 2) ((z : AdeleRing (𝓞 K) K)) * (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
  exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq.symm

end RS12L_e13

namespace RS12H

theorem isHeckeCosetSystem_comp_equiv {G : Type*} [Group G] {U : Subgroup G} {g : G} {ι κ : Type*}
    (reps : ι → G) (e : κ ≃ ι) (h : HeckeIntegralSeam.IsHeckeCosetSystem U g reps) :
    HeckeIntegralSeam.IsHeckeCosetSystem U g (reps ∘ e) where
  mem_doubleCoset := fun k => h.mem_doubleCoset (e k)
  covers := fun x hx => by
    obtain ⟨i, hi⟩ := h.covers x hx
    exact ⟨e.symm i, by simpa using hi⟩
  mk_injective := fun k₁ k₂ hk => e.injective (h.mk_injective (by simpa using hk))

end RS12H

namespace RS12T

theorem rightConv_sum_left_translate (K : Type) [Field K] [NumberField K]
    (φ f : AdelicGL2 (𝓞 K) K → ℂ) (hφ : Continuous φ) (hf : Continuous f) (hfs : HasCompactSupport f)
    {n : ℕ} (h : Fin n → AdelicGL2 (𝓞 K) K) (cs : Fin n → ℂ) (g : AdelicGL2 (𝓞 K) K) :
    rightConv K φ (fun z => ∑ i, cs i * f ((h i)⁻¹ * z)) g = ∑ i, cs i * rightConv K φ f (g * h i) := by
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  have hterm : ∀ i, Integrable (fun z => φ (g * z) * (cs i * f ((h i)⁻¹ * z))) (adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro i
    have hc2 : Continuous fun z : AdelicGL2 (𝓞 K) K => cs i * f ((h i)⁻¹ * z) :=
      continuous_const.mul (hf.comp (continuous_mul_left _))
    have hcs : HasCompactSupport fun z : AdelicGL2 (𝓞 K) K => cs i * f ((h i)⁻¹ * z) := by
      refine HasCompactSupport.mul_left ?_
      exact hfs.comp_homeomorph (Homeomorph.mulLeft (h i)⁻¹)
    exact ((hφ.comp (continuous_mul_left g)).mul hc2).integrable_of_hasCompactSupport hcs.mul_left
  simp only [rightConv]
  rw [show (fun z => φ (g * z) * ∑ i, cs i * f ((h i)⁻¹ * z)) =
      fun z => ∑ i, φ (g * z) * (cs i * f ((h i)⁻¹ * z)) from funext fun z => Finset.mul_sum _ _ _]
  rw [integral_finset_sum _ fun i _ => hterm i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← integral_const_mul]
  have key := integral_mul_left_eq_self (μ := adelicGLHaar (Fin 2) (𝓞 K) K)
    (fun z => cs i * (φ (g * z) * f ((h i)⁻¹ * z))) (h i)
  simp only [inv_mul_cancel_left] at key
  calc ∫ a, φ (g * a) * (cs i * f ((h i)⁻¹ * a)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      = ∫ a, cs i * (φ (g * a) * f ((h i)⁻¹ * a)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
        congr 1; funext a; ring
    _ = ∫ a, cs i * (φ (g * (h i * a)) * f a) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := key.symm
    _ = ∫ a, cs i * (φ (g * h i * a) * f a) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
        congr 1; funext a; rw [mul_assoc g]

theorem isFactorizableTestFn_sum_left_translate (K : Type) [Field K] [NumberField K]
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hfT : IsFactorizableTestFn K f)
    {n : ℕ} (h : Fin n → AdelicGL2 (𝓞 K) K) (hharch : ∀ i, glArch (𝓞 K) K (h i) = 1) (cs : Fin n → ℂ) :
    IsFactorizableTestFn K (fun z => ∑ i, cs i * f ((h i)⁻¹ * z)) := by
  obtain ⟨fa, ff, hfa, ⟨hffl, hffc⟩, hfeq⟩ := hfT
  refine ⟨fa, fun y => ∑ i, cs i * ff ((glFin (𝓞 K) K (h i))⁻¹ * y), hfa, ⟨?_, ?_⟩, ?_⟩
  · have hterm : ∀ i, IsLocallyConstant fun y : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
        cs i * ff ((glFin (𝓞 K) K (h i))⁻¹ * y) := fun i =>
      (IsLocallyConstant.const (cs i)).mul (hffl.comp_continuous (continuous_mul_left _))
    have : (fun y : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) => ∑ i, cs i * ff ((glFin (𝓞 K) K (h i))⁻¹ * y)) =
        ∑ i, fun y => cs i * ff ((glFin (𝓞 K) K (h i))⁻¹ * y) := by
      funext y; simp only [Finset.sum_apply]
    rw [this]
    exact Finset.sum_induction _ IsLocallyConstant (fun a b ha hb => ha.add hb)
      (IsLocallyConstant.const 0) (fun i _ => hterm i)
  · have hterm : ∀ i, HasCompactSupport fun y : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
        cs i * ff ((glFin (𝓞 K) K (h i))⁻¹ * y) := fun i =>
      (hffc.comp_homeomorph (Homeomorph.mulLeft (glFin (𝓞 K) K (h i))⁻¹)).mul_left
    have : (fun y : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) => ∑ i, cs i * ff ((glFin (𝓞 K) K (h i))⁻¹ * y)) =
        ∑ i, fun y => cs i * ff ((glFin (𝓞 K) K (h i))⁻¹ * y) := by
      funext y; simp only [Finset.sum_apply]
    rw [this]
    exact Finset.sum_induction _ HasCompactSupport (fun a b ha hb => ha.add hb)
      HasCompactSupport.zero (fun i _ => hterm i)
  · intro g
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfeq ((h i)⁻¹ * g), map_mul, map_mul, map_inv, map_inv, hharch i, inv_one, one_mul]
    ring

theorem unipotentGL2_algebraMap_eq_globalPoints (K : Type) [Field K] [NumberField K] (β : K) :
    unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) = globalPoints (𝓞 K) K (unipotentGL2 β) := by
  refine Units.ext ?_
  ext i j
  simp only [unipotentGL2_coe, globalPoints, Matrix.GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem measurable_majorant (K : Type) [Field K] [NumberField K]
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : Continuous φ) :
    Measurable (fun g : AdelicGL2 (𝓞 K) K => ‖φ g‖ +
      ∑' ξ : K, ‖φ (adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)‖) := by
  refine hφ.norm.measurable.add ?_
  haveI : Countable K :=
    Countable.of_equiv (Fin (Module.finrank ℚ K) → ℚ) (Module.finBasis ℚ K).equivFun.symm.toEquiv
  have hterm : ∀ ξ : K, Measurable fun g : AdelicGL2 (𝓞 K) K =>
      ‖φ (adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)‖₊ :=
    fun ξ => (hφ.comp (continuous_mul_left _)).nnnorm.measurable
  have h := (Measurable.nnreal_tsum hterm).coe_nnreal_real
  have hfun : (fun g : AdelicGL2 (𝓞 K) K =>
      ∑' ξ : K, ‖φ (adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)‖) =
      fun g => ((∑' ξ : K, ‖φ (adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)‖₊ : ℝ≥0) : ℝ) := by
    funext g
    rw [NNReal.coe_tsum]
    simp only [coe_nnnorm]
  rw [hfun]
  exact h

theorem glArch_unipotentGL2_eq_one (K : Type) [Field K] [NumberField K]
    (y : AdeleRing (𝓞 K) K) (hy : y.1 = 0) : glArch (𝓞 K) K (unipotentGL2 y) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicLevel.glArch_apply, unipotentGL2_coe, Units.val_one]
  fin_cases i <;> fin_cases j <;> first | rfl | simp [hy] | simp [hy, Prod.fst_one, Prod.fst_zero]

theorem under_self (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) :
    HeightOneSpectrum.under (𝓞 K) w = w := by
  apply HeightOneSpectrum.ext
  show Ideal.comap (algebraMap (𝓞 K) (𝓞 K)) w.asIdeal = w.asIdeal
  have h : algebraMap (𝓞 K) (𝓞 K) = RingHom.id (𝓞 K) := by
    ext x
    rfl
  rw [h, Ideal.comap_id]

theorem isIsotypicCuspFormAt_mono (K : Type) [Field K] [NumberField K]
    (pins : CarrierPins K) (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 K)) {S S' : Finset (HeightOneSpectrum (𝓞 K))}
    (hSS' : S ⊆ S') (Φ : HeckeEigensystem K ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (h : IsIsotypicCuspFormAt K pins ξ N S Φ φ) : IsIsotypicCuspFormAt K pins ξ N S' Φ φ where
  smoothCusp := h.smoothCusp
  continuous := h.continuous
  level_invariant := h.level_invariant
  hecke_eigen := fun v hv => h.hecke_eigen v (fun hvS => hv (hSS' hvS))
  central_eigen := fun v hv => h.central_eigen v (fun hvS => hv (hSS' hvS))

end RS12T

section
open LocalGL2 AdelicDock NumberField.AdelicLevel

namespace RS27

variable (K : Type) [Field K] [NumberField K]

theorem gl_ext {g h : AdelicGL2 (𝓞 K) K} (h₁ : glArch (𝓞 K) K g = glArch (𝓞 K) K h)
    (h₂ : ∀ u, finComponent (𝓞 K) K u (glFin (𝓞 K) K g) = finComponent (𝓞 K) K u (glFin (𝓞 K) K h)) :
    g = h := by
  apply Units.ext
  ext i j
  apply Prod.ext
  · have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing K) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) h₁) i) j
    beta_reduce at this
    rwa [glArch_apply, glArch_apply] at this
  · refine RestrictedProduct.ext _ _ fun u => ?_
    have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (u.adicCompletion K) => (m : Matrix (Fin 2) (Fin 2) (u.adicCompletion K))) (h₂ u)) i) j
    beta_reduce at this
    rwa [finComponent_apply, finComponent_apply, glFin_apply, glFin_apply] at this

theorem commute_placeEmbed_of_finComponent_eq_one {κ : AdelicGL2 (𝓞 K) K} (hκa : glArch (𝓞 K) K κ = 1)
    {v : HeightOneSpectrum (𝓞 K)} (hκv : finComponent (𝓞 K) K v (glFin (𝓞 K) K κ) = 1)
    (xv : GL (Fin 2) (v.adicCompletion K)) :
    κ * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * κ := by
  have hP : UnramifiedWhittaker.placeEmbed K v xv = AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K v xv) := rfl
  refine gl_ext K ?_ fun u => ?_
  · rw [map_mul, map_mul, hP, AdelicDock.glArch_finEmbed, hκa]
  · rw [map_mul, map_mul, map_mul, map_mul]
    by_cases hu : u = v
    · subst hu
      rw [hκv, one_mul, mul_one]
    · rw [hP, AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_of_ne _ _ _ _ hu, mul_one, one_mul]

noncomputable def evalAt (v : HeightOneSpectrum (𝓞 K)) : AdeleRing (𝓞 K) K →+* v.adicCompletion K :=
  (finAdeleEval (𝓞 K) K v).comp (adeleFin (𝓞 K) K)

theorem evalAt_eq (v : HeightOneSpectrum (𝓞 K)) (x : AdeleRing (𝓞 K) K) : x.2 v = evalAt K v x := rfl

theorem mul_comm_of_glArch_eq_one_of_glFin_eq_one {a b : AdelicGL2 (𝓞 K) K} (ha : glArch (𝓞 K) K a = 1)
    (hb : glFin (𝓞 K) K b = 1) : a * b = b * a :=
  gl_ext K (by rw [map_mul, map_mul, ha, one_mul, mul_one])
    (fun u => by rw [map_mul, map_mul, map_mul, map_mul, hb, map_one, mul_one, one_mul])

theorem glFin_diagOne_of_snd_eq_one (ε : (AdeleRing (𝓞 K) K)ˣ) (hε : ((ε : AdeleRing (𝓞 K) K)).2 = 1) :
    glFin (𝓞 K) K (diagOne ε) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glFin_apply, diagOne_coe_apply, Units.val_one]
  fin_cases i <;> fin_cases j <;> (try simp [Matrix.diagonal, Matrix.one_apply, hε]) <;> rfl

theorem det_centralScalar (z : (AdeleRing (𝓞 K) K)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z) = z * z := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul]
  change (Matrix.scalar (Fin 2) ((z : AdeleRing (𝓞 K) K))).det = _
  rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two]

end RS27

end

set_option maxHeartbeats 6400000 in

theorem solution
    (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
      (_hc : 0 < c) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
      (_hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
      (Θ : HeckeEigensystem K ℂ)
      (R : SmoothCuspRealizationAt K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral)
      (_hR : IsGenuineCuspRealizationAt K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral R)
      (tys : AutomorphicForm.ArchTypeFamily K)
      (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
      (_hV : IsCuspConstituent K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) R.centralChar V)
      (_hRV : R.toFun ∈ V ⊓ levelInvariantSubmodule K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.level ⊓ archCutSubmodule K tys),
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (f : AdelicGL2 (𝓞 K) K → ℂ) (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (w e₁ e₂ d₁' d₂' a : ℝ) (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (tset : Finset (AdelicGL2 (𝓞 K) K)),

      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ¬ v.asIdeal ∣ Θ.level ∧ v ∉ R.exceptionalSet) ∧

      IsFactorizableTestFn K f ∧
      (∀ s, IsInducedSection (𝓞 K) K (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s)) ∧
      (∀ s, IsArchKFinite K (φ s)) ∧ (∀ s, IsKfSmooth K (φ s)) ∧
      Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φ p.1 p.2) ∧
      (∀ g, Differentiable ℂ (fun s => φ s g)) ∧
      (∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K), 1 / 2 < s.re →
        Summable fun ξ : K => ‖φ s (adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)‖) ∧
      (∀ (s : ℂ) (v : HeightOneSpectrum (𝓞 K)), v ∉ S →
        ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
          φ s (g * UnramifiedWhittaker.placeEmbed K v
            (Matrix.GeneralLinearGroup.map
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = φ s g) ∧

      (∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
          (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
          0 ≤ (φ (1 / 2) k).re ∧ (φ (1 / 2) k).im = 0) ∧
      (∃ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K ∧
          (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) ∧
          φ (1 / 2) k ≠ 0) ∧

      0 < e₁ ∧ e₁ < e₂ ∧ MeasurableSet 𝓕 ∧
      𝓕 ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂} ∧
      IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
          {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}) ∧
      0 < d₁' ∧ 𝓕 ⊆ (⋃ t ∈ tset, (· * t) '' centreCutSiegelSet K c u d₁' d₂') ∧

      Continuous (rightConv K R.toFun f) ∧ IsKfSmooth K (rightConv K R.toFun f) ∧
      @IsCuspidalFn _ (adeleBorel (𝓞 K) K) _ _
        (@ProbabilityTheory.cond _ (adeleBorel (𝓞 K) K) (adelicAddHaar (𝓞 K) K) (adelicBox K))
        unipotentGL2 (rightConv K R.toFun f) ∧
      (∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
        rightConv K R.toFun f (globalPoints (𝓞 K) K γ * g) = rightConv K R.toFun f g) ∧
      (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
        rightConv K R.toFun f (centralScalar (𝓞 K) K z * g) =
          ((R.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * rightConv K R.toFun f g) ∧
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ‖((R.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w) ∧
      (∀ g, whittakerCoefficient K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) 0 g = 0) ∧
      (∀ g, Summable fun b : K => ‖whittakerCoefficient K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) b g‖) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
          rightConv K R.toFun f (g * UnramifiedWhittaker.placeEmbed K v
            (Matrix.GeneralLinearGroup.map
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = rightConv K R.toFun f g) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        IsHeckeCosetEigenfunctionAt K (levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K)
          (heckeGen (𝓞 K) K v) v (rightConv K R.toFun f) (Θ.toRawCentral.a v)) ∧

      (∃ κ : ℝ, ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ‖Θ.a v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
        ‖Θ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ g : AdelicGL2 (𝓞 K) K,
        Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
          (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
               (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2 →
        ∀ m : ℕ,
          whittakerCoefficient K
              (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
                (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) 1
              ((heckeGen (𝓞 K) K v) ^ m * g) *
            (starRingEnd ℂ) (whittakerCoefficient K
              (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
                (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) 1
              ((heckeGen (𝓞 K) K v) ^ m * g)) =
          UnramifiedWhittaker.heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (Θ.a v)
              (Θ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) m *
            UnramifiedWhittaker.heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ((starRingEnd ℂ) (Θ.a v))
              ((starRingEnd ℂ) (Θ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ))) m *
            (whittakerCoefficient K
                (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
                  (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                  (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) 1 g *
              (starRingEnd ℂ) (whittakerCoefficient K
                (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
                  (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                  (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) 1 g))) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ g : AdelicGL2 (𝓞 K) K,
        Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
          (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
               (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2 →
        ∀ m : ℕ, 0 < m →
          whittakerCoefficient K
              (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
                (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) 1
              ((heckeGen (𝓞 K) K v)⁻¹ ^ m * g) = 0) ∧

      (∀ t ∈ tset, ∀ N : ℕ, IntegrableOn
        (fun g => ‖rightConv K R.toFun f g‖ * ‖rightConv K R.toFun f g‖ *
          (1 + archHeight K (glArch (𝓞 K) K (g * t⁻¹))) ^ N *
          NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w))
        (𝓕 ∩ (· * t) '' centreCutSiegelSet K c u d₁' d₂') (adelicGLHaar (Fin 2) (𝓞 K) K)) ∧

      (∀ s : ℂ, 1 / 2 < s.re → IntegrableOn (fun g => ‖rightConv K R.toFun f g‖ ^ 2 *
          (‖φ s g‖ + ∑' ξ : K, ‖φ s (adelicWeyl (𝓞 K) K *
            unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)‖) *
          NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w)) 𝓕
          (adelicGLHaar (Fin 2) (𝓞 K) K)) ∧

      peterssonIntegral K w 𝓕 (rightConv K R.toFun f) (rightConv K R.toFun f) ≠ 0 ∧

      a < 1 / 2 ∧
      AnalyticOnNhd ℂ (fun s : ℂ => RankinSelberg.sPartIntegral K S
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) (rightConv K R.toFun f) (φ s) w e₁ e₂)
        {s : ℂ | a < s.re} ∧
      (∀ σ : ℝ, a < σ →
        (RankinSelberg.sPartIntegral K S
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) (rightConv K R.toFun f) (φ σ) w e₁ e₂).im = 0 ∧
        0 < (RankinSelberg.sPartIntegral K S
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) (rightConv K R.toFun f) (φ σ) w e₁ e₂).re) := by
  intro α hα c u d₁ d₂ T hc hd₁ hd hcov Θ R hR tys V hV hRV
  have hN : Θ.level ≠ ⊥ := Θ.level_ne_bot
  obtain ⟨⟨hRV', hRlev⟩, hRt⟩ := hRV
  have hRne : ∃ g, R.toFun g ≠ 0 := R.exists_ne_zero
  obtain ⟨f, hfT, hfBF, hfbi, ⟨Sf, hNSf, hftier, hfsupp⟩, g₀, hx₀ne⟩ :=
    AutomorphicForm.exists_isUnitFactorizableAboveOfType_biInvariant_rightConv_ne_zero_of_mem_archCutSubmodule
      K Θ.level hN tys R.toFun hR hRne (fun g k hk => hRlev g k hk) hRt
  have hx₀V : rightConv K R.toFun f ∈ V := hV.1.rightConv_mem f tys hfT hfBF R.toFun hRV'
  obtain ⟨hICC, hmod, hcontImp⟩ := AutomorphicForm.SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine K
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)
    Θ.toRawCentral R
  set ωR : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom with hωRdef
  have hωR_apply : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ωR z = R.centralChar ⟨z, Subgroup.mem_top z⟩ := fun z => rfl
  obtain ⟨w, hω⟩ := NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow K ωR hICC (hcontImp hR)
  have hω' : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((R.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w :=
    fun z => by rw [← hωR_apply]; exact hω z
  obtain ⟨d₁', d₂', tset, 𝓕, hd₁', h𝓕m, h𝓕s, h𝓕, h𝓕covC⟩ :=
    AutomorphicForm.exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre
      K c u d₁ d₂ T hc hd₁ hd hcov 1 2 one_pos one_lt_two
  have hSψ : ∃ Sψ : Finset (HeightOneSpectrum (𝓞 K)), ∀ v ∉ Sψ,
      LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K v) = 0 := by
    have hfin := FractionalIdeal.finite_factors (K := K)
      ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
    rw [Filter.eventually_cofinite] at hfin
    refine ⟨hfin.toFinset, fun v hv => ?_⟩
    by_contra hne
    refine hv (hfin.mem_toFinset.mpr ?_)
    rwa [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal] at hne
  obtain ⟨Sψ, hSψ0⟩ := hSψ
  set S : Finset (HeightOneSpectrum (𝓞 K)) := Sf ∪ R.exceptionalSet ∪ Sψ with hSdef
  have hSf_sub : Sf ⊆ S := fun v hv => by simp [hSdef, hv]
  have hS_good : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ¬ v.asIdeal ∣ Θ.level ∧ v ∉ R.exceptionalSet := by
    intro v hv
    refine ⟨fun hdvd => hv ?_, fun hex => hv ?_⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hNSf v hdvd))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hex)
  obtain ⟨hx₀c, hx₀smooth⟩ :=
    AutomorphicForm.CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule K
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) R.centralChar (rightConv K R.toFun f) (hV.1.le hx₀V)
  have hx₀1 : IsSmoothCuspAutomorphicFnAt K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) R.centralChar (rightConv K R.toFun f) := by
    have h1 := hx₀smooth 1
    have : rightTranslate K (1 : AdelicGL2 (𝓞 K) K) (rightConv K R.toFun f) = rightConv K R.toFun f :=
      funext fun y => by simp [rightTranslate_apply]
    rwa [this] at h1
  have hx₀G : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      rightConv K R.toFun f (globalPoints (𝓞 K) K γ * g) = rightConv K R.toFun f g := by
    letI := (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).mS
    letI : MeasureSpace (AdelicGL2 (𝓞 K) K) := ⟨(productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).μ⟩
    exact hx₀1.1.1.left_invariant
  have hx₀per : ∀ (β : K) (uu : AdeleRing (𝓞 K) K) (hh : AdelicGL2 (𝓞 K) K),
      rightConv K R.toFun f (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + uu) * hh) =
        rightConv K R.toFun f (unipotentGL2 uu * hh) := by
    intro β uu hh
    rw [unipotentGL2_add, mul_assoc, RS12T.unipotentGL2_algebraMap_eq_globalPoints, hx₀G]
  have hx₀leftN : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K),
      rightConv K R.toFun f (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = rightConv K R.toFun f g := by
    intro β g
    rw [RS12T.unipotentGL2_algebraMap_eq_globalPoints]
    exact hx₀G _ g
  have hx₀int : ∀ (α' : K) (g : AdelicGL2 (𝓞 K) K), WhittakerCoefficientIntegrable K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
      (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) α' g :=
    (AutomorphicForm.whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace K
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) _ (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K) _ hx₀leftN hx₀1.2
      (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn K R.toFun hR f hfT).2).1
  have hUv : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ kv : GL (Fin 2) (v.adicCompletionIntegers K),
      UnramifiedWhittaker.placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv) ∈
        levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K := by
    intro v hv kv
    obtain ⟨hlv, -⟩ := hS_good v hv
    set k : GL (Fin 2) (v.adicCompletion K) := Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv with hkdef
    have hk : ∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K := by
      intro i j
      show (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) ((kv : Matrix (Fin 2) (Fin 2) _) i j) ∈ _
      exact SetLike.coe_mem _
    have hk' : ∀ i j, ((k⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
        ∈ v.adicCompletionIntegers K := by
      intro i j
      have : k⁻¹ = Matrix.GeneralLinearGroup.map
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv⁻¹ := by rw [hkdef, map_inv]
      rw [this]
      show (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) (((kv⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) i j) ∈ _
      exact SetLike.coe_mem _
    have hb : idealBound (𝓞 K) Θ.level v = 1 := idealBound_eq_one_of_not_dvd hN hlv
    show AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K v k) ∈ _
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [AdelicDock.finEmbed_mem_levelOne_iff, AdelicDock.localEmbed_mem_finiteLevelOne_iff,
        AdelicDock.mem_localLevelOne_iff]
      refine ⟨⟨hk, ?_, ?_⟩, ⟨hk', ?_, ?_⟩⟩ <;> rw [hb]
      · simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using hk 1 0
      · simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using sub_mem (hk 1 1) (one_mem _)
      · simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using hk' 1 0
      · simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using sub_mem (hk' 1 1) (one_mem _)
    · rw [mem_finiteAdelicGL2Subgroup_iff, AdelicDock.glArch_finEmbed]
  have hpure : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 K) K,
        IsHeckeCosetSystem (levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K) (heckeGen (𝓞 K) K v) reps ∧
        ∀ j, ∃ m : GL (Fin 2) (v.adicCompletion K), reps j = UnramifiedWhittaker.placeEmbed K v m := by
    intro v hv
    obtain ⟨hlv, -⟩ := hS_good v hv
    obtain ⟨ϖ, hϖ0, -, -, sec, -, hsysAll⟩ := HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen K v
    haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
    letI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
    have hcard : Fintype.card (𝓞 K ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
      rw [← Nat.card_eq_fintype_card, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have hcardO : Fintype.card (Option (𝓞 K ⧸ v.asIdeal)) = Ideal.absNorm v.asIdeal + 1 := by
      rw [Fintype.card_option, hcard]
    set eO : Option (𝓞 K ⧸ v.asIdeal) ≃ Fin (Ideal.absNorm v.asIdeal + 1) := Fintype.equivFinOfCardEq hcardO with heO
    set repsL : Option (𝓞 K ⧸ v.asIdeal) → AdelicGL2 (𝓞 K) K := fun o => AdelicDock.finEmbed (𝓞 K) K
      (AdelicDock.localEmbed (𝓞 K) K v (o.elim (LocalGL2.localRepInf ϖ hϖ0) (fun c' => LocalGL2.localRepSome ϖ hϖ0
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec c'))))) with hrepsL
    refine ⟨repsL ∘ eO.symm, RS12H.isHeckeCosetSystem_comp_equiv repsL eO.symm (hsysAll Θ.level hlv), fun j => ?_⟩
    simp only [hrepsL, Function.comp]
    exact ⟨_, rfl⟩
  have hx₀lev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K,
      rightConv K R.toFun f (g * k) = rightConv K R.toFun f g := by
    intro g k hk
    obtain ⟨hfc, hfcs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K f hfT
    have key := RS12T.rightConv_sum_left_translate K R.toFun f hR hfc hfcs (fun _ : Fin 1 => k) (fun _ => 1) g
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, one_mul] at key
    rw [← key]
    congr 1
    funext z
    exact ((hfbi k⁻¹ (inv_mem hk) z).1)
  have hx₀arch : rightConv K R.toFun f ∈ archCutSubmodule K tys := by
    have hmapI : ∀ (φr : 𝓞 K →+* 𝓞 K), (∀ x, φr x = x) → Ideal.map φr Θ.level = Θ.level := by
      intro φr hφr
      have h : φr = RingHom.id (𝓞 K) := RingHom.ext hφr
      rw [h, Ideal.map_id]
    set SL : Finset (HeightOneSpectrum (𝓞 K)) := Sf ∪ R.exceptionalSet with hSL
    have hiso0 : R.toFun ∈ isotypicCuspSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) R.centralChar Θ.level SL Θ := by
      refine IsIsotypicCuspFormAt.mem_isotypicCuspSubmodule ?_
      exact RS12T.isIsotypicCuspFormAt_mono K _ R.centralChar Θ.level Finset.subset_union_right Θ R.toFun
        (R.isIsotypicCuspFormAt hR)
    have hunder : ∀ w : HeightOneSpectrum (𝓞 K), HeightOneSpectrum.under (𝓞 K) w ∈ Sf → w ∈ SL := by
      intro w hw
      rw [RS12T.under_self] at hw
      exact Finset.mem_union_left _ hw
    have h6 := AutomorphicForm.convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType K K
      c u d₁ d₂ T hd hc hd₁ hcov R.centralChar Θ.level Sf SL hunder hNSf Θ tys f
      (by rw [hmapI _ (fun x => rfl)]; exact hftier) R.toFun
      ⟨by rw [hmapI _ (fun x => rfl)]; exact hiso0, hRt⟩
    exact h6.2
  have hx₀cut : rightConv K R.toFun f ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.level ⊓ archCutSubmodule K tys :=
    ⟨⟨hx₀V, fun g k hk => hx₀lev g k hk⟩, hx₀arch⟩
  have hSψ_sub : Sψ ⊆ S := fun v hv => by simp [hSdef, hv]
  obtain ⟨t₀, k₀, hk₀, ht₀, hWpt⟩ :=
    AutomorphicForm.SmoothCuspRealizationAt.exists_mem_maximalCompactAt_whittakerCoefficient_rightConv_diagOne_mul_ne_zero
      K c u d₁ d₂ T Θ R hR (fun g k hk => hRlev g k hk) f hfT S Sf Sψ hSf_sub hSψ_sub hfsupp hS_good hSψ0 hfbi hx₀1 ⟨g₀, hx₀ne⟩
  set κ : AdelicGL2 (𝓞 K) K := AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K k₀) with hκdef
  have hκarch : glArch (𝓞 K) K κ = 1 := AdelicDock.glArch_finEmbed _ _ _
  have hκfin : glFin (𝓞 K) K κ = glFin (𝓞 K) K k₀ := AdelicDock.glFin_finEmbed _ _ _
  have hκv : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → finComponent (𝓞 K) K v (glFin (𝓞 K) K κ) = 1 := fun v hv => by
    rw [hκfin]; exact (mem_maximalCompactAt_iff.mp hk₀).2 v hv
  have hκcomm : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ xv : GL (Fin 2) (v.adicCompletion K),
      κ * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * κ :=
    fun v hv xv => RS27.commute_placeEmbed_of_finComponent_eq_one K hκarch (hκv v hv) xv
  have ht₀ne : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v ((((t₀ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) ≠ 0 := by
    intro v
    rw [Valuation.ne_zero_iff, RS27.evalAt_eq]
    exact (Units.map (RS27.evalAt K v : AdeleRing (𝓞 K) K →* v.adicCompletion K) t₀).ne_zero
  set aexp : HeightOneSpectrum (𝓞 K) → ℤ := fun v => Multiplicative.toAdd (WithZero.unzero (ht₀ne v)) with haexp
  have haexp_spec : ∀ v, Valued.v ((((t₀ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
      ((Multiplicative.ofAdd (aexp v) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := fun v => by
    simp only [haexp, ofAdd_toAdd, WithZero.coe_unzero]
  obtain ⟨mK, ys, MK, hys, hKU⟩ :=
    AutomorphicForm.CuspidalConstituent.exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_of_isCuspConstituent
      K c u d₁ d₂ T hc hd₁ hd hcov R.centralChar Θ.level hN tys V hV (rightConv K R.toFun f) hx₀cut w hω'
  have hysκ : ∀ i : Fin mK, ∃ cB : HeightOneSpectrum (𝓞 K) → ℤ, ∀ bb : (AdeleRing (𝓞 K) K)ˣ,
      (∃ v : HeightOneSpectrum (𝓞 K), WithZero.exp (cB v) < Valued.v ((((bb : AdeleRing (𝓞 K) K)).2) v)) →
      whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightTranslate K κ (ys i)) 1 (diagOne bb) = 0 := by
    intro i
    obtain ⟨-, hsm⟩ :=
      AutomorphicForm.CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule K
        (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) R.centralChar (ys i) (hV.1.le (hys i).1.1)
    have hleft : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K),
        rightTranslate K κ (ys i) (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = rightTranslate K κ (ys i) g := by
      intro β g
      letI := (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).mS
      letI : MeasureSpace (AdelicGL2 (𝓞 K) K) := ⟨(productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).μ⟩
      rw [RS12T.unipotentGL2_algebraMap_eq_globalPoints]
      exact (hsm κ).1.1.left_invariant _ g
    obtain ⟨cB, -, hcB⟩ := AutomorphicForm.exists_whittakerCoefficient_one_diagOne_eq_zero_of_exp_lt_valuation K
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) (NumberField.StandardAddChar.stdAddChar K)
      (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K) (rightTranslate K κ (ys i)) hleft (hsm κ).2
    exact ⟨cB, hcB⟩
  choose cB hcB using hysκ
  set m : ℕ := (Finset.univ.sup fun i : Fin mK => S.sup fun v => (cB i v).toNat) with hmdef
  have hm_ge : ∀ (i : Fin mK) (v : HeightOneSpectrum (𝓞 K)), v ∈ S → cB i v ≤ (m : ℤ) := by
    intro i v hv
    have h1 : (cB i v).toNat ≤ m := by
      rw [hmdef]
      exact (Finset.le_sup (f := fun v => (cB i v).toNat) hv).trans
        (Finset.le_sup (f := fun i : Fin mK => S.sup fun v => (cB i v).toNat) (Finset.mem_univ i))
    calc cB i v ≤ ((cB i v).toNat : ℤ) := Int.self_le_toNat _
      _ ≤ (m : ℤ) := by exact_mod_cast h1
  have hboxvan : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
      (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
      ∀ t : (AdeleRing (𝓞 K) K)ˣ,
        (∃ v ∈ S, ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) <
          Valued.v ((((t : AdeleRing (𝓞 K) K)).2) v)) →
        whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) 1
          (diagOne t * k * κ) = 0 := by
    intro k hkf hka t ht
    obtain ⟨cs', ε, hε2, -, -, hexp⟩ := hKU k hkf hka
    have hkκ : k * κ = κ * k := (RS27.mul_comm_of_glArch_eq_one_of_glFin_eq_one K hκarch hkf).symm
    have hκε : κ * diagOne ε = diagOne ε * κ :=
      RS27.mul_comm_of_glArch_eq_one_of_glFin_eq_one K hκarch (RS27.glFin_diagOne_of_snd_eq_one K ε hε2)
    rw [mul_assoc, hkκ, ← mul_assoc, hexp (diagOne t * κ)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [mul_assoc, hκε, ← mul_assoc, ← map_mul,
      RS12W.whittakerCoefficient_mul_right K _ _ (ys i) 1 (diagOne (t * ε)) κ]
    have hfun : (fun y => ys i (y * κ)) = rightTranslate K κ (ys i) := funext fun y => by simp [rightTranslate_apply]
    rw [hfun, hcB i (t * ε) ?_, mul_zero]
    obtain ⟨v, hv, hlt⟩ := ht
    refine ⟨v, lt_of_le_of_lt (b := ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) ?_ ?_⟩
    · exact WithZero.coe_le_coe.mpr (Multiplicative.ofAdd_le.mpr (hm_ge i v hv))
    · have hεv : ((ε : AdeleRing (𝓞 K) K)).2 v = 1 := by rw [hε2]; rfl
      rwa [Units.val_mul, RS27.evalAt_eq, map_mul, ← RS27.evalAt_eq, ← RS27.evalAt_eq, hεv, mul_one]
  set x₀κ : AdelicGL2 (𝓞 K) K → ℂ := fun g => rightConv K R.toFun f (g * κ) with hx₀κdef
  have hx₀κper : ∀ (β : K) (uu : AdeleRing (𝓞 K) K) (hh : AdelicGL2 (𝓞 K) K),
      x₀κ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + uu) * hh) = x₀κ (unipotentGL2 uu * hh) := by
    intro β uu hh
    have hh' := hx₀per β uu (hh * κ)
    simp only [hx₀κdef, mul_assoc] at hh' ⊢
    exact hh'
  have hx₀κint : ∀ (α' : K) (g : AdelicGL2 (𝓞 K) K), WhittakerCoefficientIntegrable K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
      (NumberField.StandardAddChar.stdAddChar K) x₀κ α' g := by
    intro α' g
    simpa [WhittakerCoefficientIntegrable, hx₀κdef, mul_assoc] using hx₀int α' (g * κ)
  obtain ⟨r, y, cs, hysupp, hycomm, hWmult, hμbox⟩ :=
    AutomorphicForm.exists_unipotent_surgery_whittakerCoefficient_diagOne_mul_eq_sum_mul_shell K
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) x₀κ hx₀κper hx₀κint S m aexp
  set h : Fin r → AdelicGL2 (𝓞 K) K := fun i => unipotentGL2 (y i) * κ with hhdef
  have hharch : ∀ i, glArch (𝓞 K) K (h i) = 1 := fun i => by
    simp only [hhdef, map_mul, RS12T.glArch_unipotentGL2_eq_one K (y i) (hysupp i).1, hκarch, one_mul]
  have hhcomm : ∀ i, ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ xv : GL (Fin 2) (v.adicCompletion K),
      h i * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * h i := by
    intro i v hv xv
    simp only [hhdef]
    rw [mul_assoc, hκcomm v hv xv, ← mul_assoc, hycomm i v hv xv, mul_assoc]
  set f' : AdelicGL2 (𝓞 K) K → ℂ := fun z => ∑ i, cs i * f ((h i)⁻¹ * z) with hf'def
  set x : AdelicGL2 (𝓞 K) K → ℂ := rightConv K R.toFun f' with hxdef
  have hxsum : ∀ g, x g = ∑ i, cs i * rightConv K R.toFun f (g * h i) := by
    intro g
    obtain ⟨hfc, hfcs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K f hfT
    exact RS12T.rightConv_sum_left_translate K R.toFun f hR hfc hfcs h cs g
  obtain ⟨nS, hnS0, hxlow⟩ :=
    AutomorphicForm.exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate K Θ.level hN S
      (rightConv K R.toFun f) hx₀lev r h cs x hxsum
  have hsect : ∃ φ₀ : AdelicGL2 (𝓞 K) K → ℂ,
      IsInducedSection (𝓞 K) K (etaFst 1 α hα (1 / 2)) (etaSnd 1 α hα (1 / 2)) φ₀ ∧
      Continuous φ₀ ∧ IsArchKFinite K φ₀ ∧ IsKfSmooth K φ₀ ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
          φ₀ (g * UnramifiedWhittaker.placeEmbed K v
            (Matrix.GeneralLinearGroup.map
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = φ₀ g) ∧
      (∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
        φ₀ k = 0 ∨ φ₀ k = 1) ∧
      φ₀ 1 = 1 ∧
      (∀ (g k : AdelicGL2 (𝓞 K) K), glFin (𝓞 K) K k = 1 →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
        φ₀ (g * k) = φ₀ g) ∧
      (∀ k : AdelicGL2 (𝓞 K) K,
        (∃ v ∈ S, ¬ Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
            Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
              ((Multiplicative.ofAdd (-(nS : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        φ₀ k = 0) := by
    obtain ⟨hφ₀ind, hφ₀c, hφ₀K, hφ₀f, -, hφ₀sph, hφ₀arch, hφ₀val, hφ₀one⟩ :=
      AutomorphicForm.isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow K hα (1 / 2) S (fun _ => nS)
        (fun _ _ => hnS0)
    refine ⟨_, hφ₀ind, hφ₀c, hφ₀K, hφ₀f, hφ₀sph, hφ₀val, hφ₀one, hφ₀arch, fun k hk => ?_⟩
    obtain ⟨v, hv, hnot⟩ := hk
    exact if_neg fun hall => hnot (hall v hv)
  obtain ⟨φ₀, hφ₀ind, hφ₀c, hφ₀K, hφ₀f, hφ₀sph, hφ₀val, hφ₀one, hφ₀arch, hφ₀supp⟩ := hsect
  obtain ⟨φ, hφhalf, hφ, hφK, hφf, hφjc, hφhol, hφflat⟩ :=
    AutomorphicForm.exists_flat_isInducedSection_family_eq_of_isInducedSection K hα 1 1 (1 / 2) _ hφ₀ind hφ₀K hφ₀f hφ₀c
  have hU1 : IsUnitaryChar (𝓞 K) K (1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := fun t => by simp
  have hφc : ∀ s, Continuous (φ s) := fun s => hφjc.comp (Continuous.prodMk continuous_const continuous_id)
  have hφsum : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K), 1 / 2 < s.re →
      Summable (fun ξ : K => ‖φ s (adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)‖) :=
    fun s g hs => AutomorphicForm.bruhatTransversal_summand_norm_summable_of_re_gt_half K hα 1 1 hU1 hU1 s hs (φ s) (hφ s) (hφc s) g
  have hφsph : ∀ (s : ℂ) (v : HeightOneSpectrum (𝓞 K)), v ∉ S →
      ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
        φ s (g * UnramifiedWhittaker.placeEmbed K v
          (Matrix.GeneralLinearGroup.map
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = φ s g := by
    intro s v hv kv g
    set kk := UnramifiedWhittaker.placeEmbed K v (Matrix.GeneralLinearGroup.map
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv) with hkk
    have hind' : IsInducedSection (𝓞 K) K (etaFst 1 α hα s) (etaSnd 1 α hα s) (fun g => φ s (g * kk)) :=
      (hφ s).rightTranslate kk
    have key := AutomorphicForm.IsInducedSection.eq_of_eqOn_maximalCompact K (etaFst 1 α hα s) (etaSnd 1 α hα s)
      (fun g => φ s (g * kk)) (φ s) hind' (hφ s) ?_
    · exact congrFun key g
    · intro k hkf hka
      set kloc : GL (Fin 2) (v.adicCompletion K) := Matrix.GeneralLinearGroup.map
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv with hkloc
      have hkk_eq : kk = AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K v kloc) := rfl
      have hint_k : ∀ i j, (kloc : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K := by
        intro i j
        show (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) ((kv : Matrix (Fin 2) (Fin 2) _) i j) ∈ _
        exact SetLike.coe_mem _
      have hint_k' : ∀ i j, ((kloc⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
          ∈ v.adicCompletionIntegers K := by
        intro i j
        have : kloc⁻¹ = Matrix.GeneralLinearGroup.map
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv⁻¹ := by rw [hkloc, map_inv]
        rw [this]
        show (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) (((kv⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) i j) ∈ _
        exact SetLike.coe_mem _
      have hkkfin : glFin (𝓞 K) K kk ∈ finiteIntegralGL2 (𝓞 K) K := by
        rw [hkk_eq, AdelicDock.glFin_finEmbed]
        refine finiteLevelOne_le_finiteLevelZero (𝓞 K) K ⊤ ?_
        rw [AdelicDock.localEmbed_mem_finiteLevelOne_iff, AdelicDock.mem_localLevelOne_iff]
        refine ⟨⟨hint_k, ?_, ?_⟩, ⟨hint_k', ?_, ?_⟩⟩ <;> rw [idealBound_top]
        · simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using hint_k 1 0
        · simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using sub_mem (hint_k 1 1) (one_mem _)
        · simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using hint_k' 1 0
        · simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using sub_mem (hint_k' 1 1) (one_mem _)
      have hkkarch : glArch (𝓞 K) K kk = 1 := by rw [hkk_eq, AdelicDock.glArch_finEmbed]
      have hprod_fin : glFin (𝓞 K) K (k * kk) ∈ finiteIntegralGL2 (𝓞 K) K := by
        rw [map_mul]; exact mul_mem hkf hkkfin
      have hprod_arch : ∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K (k * kk))) := by
        intro w'; rw [map_mul, hkkarch, mul_one]; exact hka w'
      show φ s (k * kk) = φ s k
      rw [hφflat s (1 / 2) (k * kk) hprod_fin hprod_arch, hφflat s (1 / 2) k hkf hka, hφhalf]
      exact hφ₀sph v hv kv k
  have hxV : x ∈ V := by
    have hfun : x = ∑ i, cs i • rightTranslate K (h i) (rightConv K R.toFun f) := by
      funext g
      rw [hxsum g, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [rightTranslate_apply, smul_eq_mul]
    rw [hfun]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    exact hV.1.rightTranslate_fin_mem (h i) ((mem_finiteAdelicGL2Subgroup_iff K (h i)).mpr (hharch i)) _ hx₀V
  have hf'T : IsFactorizableTestFn K f' := RS12T.isFactorizableTestFn_sum_left_translate K f hfT h hharch cs
  have hdecay : ∀ t ∈ tset, ∀ N : ℕ, IntegrableOn
      (fun g => ‖x g‖ * ‖x g‖ * (1 + archHeight K (glArch (𝓞 K) K (g * t⁻¹))) ^ N *
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w))
      (𝓕 ∩ (· * t) '' centreCutSiegelSet K c u d₁' d₂') (adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro t ht N
    have key := AutomorphicForm.integrableOn_norm_rightConv_sq_mul_archHeight_pow_mul_ideleNorm_rpow_inter_centreCutSiegelSet K
      c u d₁ d₂ T hd hcov R.centralChar R.toFun R.smoothCusp.1 hR f' hf'T w 1 2 one_pos one_lt_two 𝓕 h𝓕m h𝓕s h𝓕 c u d₁' d₂' hc hd₁' t N
    have hfun : (fun g => ‖x g‖ * ‖x g‖ * (1 + archHeight K (glArch (𝓞 K) K (g * t⁻¹))) ^ N *
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w)) =
        (fun g => ‖rightConv K R.toFun f' g‖ ^ 2 * (1 + archHeight K (glArch (𝓞 K) K (g * t⁻¹))) ^ N *
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w)) := by
      funext g; simp only [hxdef, sq]
    rw [hfun]; exact key
  obtain ⟨hxc, hxsmooth⟩ :=
    AutomorphicForm.CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule K
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) R.centralChar x (hV.1.le hxV)
  have hx1 : IsSmoothCuspAutomorphicFnAt K _ R.centralChar x := by
    have h1 := hxsmooth 1
    have : rightTranslate K (1 : AdelicGL2 (𝓞 K) K) x = x := funext fun y => by simp [rightTranslate_apply]
    rwa [this] at h1
  have hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      x (globalPoints (𝓞 K) K γ * g) = x g := by
    letI := (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).mS
    letI : MeasureSpace (AdelicGL2 (𝓞 K) K) := ⟨(productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).μ⟩
    exact hx1.1.1.left_invariant
  have hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x (centralScalar (𝓞 K) K z * g) = ((R.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x g := by
    letI := (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).mS
    letI : MeasureSpace (AdelicGL2 (𝓞 K) K) := ⟨(productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).μ⟩
    intro z g
    exact hx1.1.1.central_transform ⟨z, Subgroup.mem_top z⟩ g
  have hPne : peterssonIntegral K w 𝓕 x x ≠ 0 := by
    refine AutomorphicForm.peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous K w 1 2 one_pos one_lt_two
      𝓕 h𝓕m h𝓕s h𝓕 x ?_ ?_ ?_ ?_
    · exact hxc
    · exact hxG
    ·
      have hk₀f : glFin (𝓞 K) K (k₀ * κ⁻¹) = 1 := by rw [map_mul, map_inv, hκfin, mul_inv_cancel]
      have hk₀a : ∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K (k₀ * κ⁻¹))) := by
        intro pl
        rw [map_mul, map_inv, hκarch, inv_one, mul_one]
        exact (mem_adelicMaximalCompact_iff.mp (maximalCompactAt_le K S hk₀)).2 pl
      have hk₀κ : k₀ * κ⁻¹ * κ = k₀ := inv_mul_cancel_right _ _
      have ht₀box : ∀ v ∈ S, Valued.v ((((t₀ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) ≤
          ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
        intro v hv
        by_contra hlt
        rw [not_le] at hlt
        have h0 := hboxvan (k₀ * κ⁻¹) hk₀f hk₀a t₀ ⟨v, hv, hlt⟩
        rw [mul_assoc, hk₀κ] at h0
        exact hWpt h0
      have hxfun : x = fun g => ∑ i, cs i * x₀κ (g * unipotentGL2 (y i)) := by
        funext g
        rw [hxsum g]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hhdef, hx₀κdef, mul_assoc]
      have hcommk : ∀ i, (k₀ * κ⁻¹) * unipotentGL2 (y i) = unipotentGL2 (y i) * (k₀ * κ⁻¹) := fun i =>
        (RS27.mul_comm_of_glArch_eq_one_of_glFin_eq_one K (RS12T.glArch_unipotentGL2_eq_one K (y i) (hysupp i).1) hk₀f).symm
      have hmul := hWmult t₀ (k₀ * κ⁻¹) hcommk
      have hμ1 := hμbox t₀ ht₀box
      rw [if_pos (fun v _ => haexp_spec v)] at hμ1
      rw [← hxfun, hμ1, one_mul] at hmul
      have hW₁x₀κ : whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀κ 1 (diagOne t₀ * (k₀ * κ⁻¹)) =
          whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) 1 (diagOne t₀ * k₀) := by
        rw [hx₀κdef, ← RS12W.whittakerCoefficient_mul_right K _ _ (rightConv K R.toFun f) 1 (diagOne t₀ * (k₀ * κ⁻¹)) κ,
          mul_assoc, hk₀κ]
      have hxne : ∃ g₁, x g₁ ≠ 0 := by
        by_contra hall
        push_neg at hall
        have hx0 : x = fun _ => 0 := funext hall
        have hW0 : whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 (diagOne t₀ * (k₀ * κ⁻¹)) = 0 := by
          rw [hx0]; simp only [whittakerCoefficient, zero_mul, MeasureTheory.integral_zero]
        rw [hW0] at hmul
        have hz : whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K)
            (rightConv K R.toFun f) 1 (diagOne t₀ * k₀) = 0 := by rw [← hW₁x₀κ]; exact hmul.symm
        exact hWpt hz
      obtain ⟨g₁, hg₁⟩ := hxne
      have h32 : (0 : ℝ) < 3 / 2 / NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g₁) :=
        div_pos (by norm_num) (NumberField.TateGlobal.ideleNorm_pos _)
      obtain ⟨z, -, hzn⟩ := NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one K _ (Real.sqrt_pos.mpr h32)
      refine ⟨centralScalar (𝓞 K) K z * g₁, ?_, ?_⟩
      · have hdet : Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z * g₁) =
            z * z * Matrix.GeneralLinearGroup.det g₁ := by
          rw [map_mul, RS27.det_centralScalar]
        rw [hdet, NumberField.TateGlobal.ideleNorm_mul, NumberField.TateGlobal.ideleNorm_mul, hzn,
          Real.mul_self_sqrt h32.le, div_mul_cancel₀ _ (NumberField.TateGlobal.ideleNorm_pos _).ne']
        constructor <;> norm_num
      · rw [hxZ z g₁]
        exact mul_ne_zero (Units.ne_zero _) hg₁
    ·
      have hcov𝓕 : 𝓕 = ⋃ t ∈ tset, (𝓕 ∩ (· * t) '' centreCutSiegelSet K c u d₁' d₂') := by
        apply Set.Subset.antisymm
        · intro g hg
          have := h𝓕covC hg
          simp only [Set.mem_iUnion] at this ⊢
          obtain ⟨t, ht, hgt⟩ := this
          exact ⟨t, ht, hg, hgt⟩
        · intro g hg
          simp only [Set.mem_iUnion] at hg
          obtain ⟨t, -, hg, -⟩ := hg
          exact hg
      rw [hcov𝓕]
      refine (integrableOn_finset_iUnion).mpr fun t ht => ?_
      have h0 := hdecay t ht 0
      refine h0.congr_fun (fun g _ => ?_) (h𝓕m.inter
        ((Homeomorph.mulRight t).measurableEmbedding.measurableSet_image.mpr (measurableSet_centreCutSiegelSet c u d₁' d₂')))
      simp only [pow_zero, mul_one, sq]
  have hmaj : ∀ s : ℂ, 1 / 2 < s.re → IntegrableOn
      (fun g => ‖x g‖ ^ 2 * (‖φ s g‖ + ∑' ξ : K, ‖φ s (adelicWeyl (𝓞 K) K *
          unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)‖) *
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w)) 𝓕 (adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro s hs
    have hcov𝓕 : 𝓕 = ⋃ t ∈ tset, (𝓕 ∩ (· * t) '' centreCutSiegelSet K c u d₁' d₂') := by
      apply Set.Subset.antisymm
      · intro g hg
        have := h𝓕covC hg
        simp only [Set.mem_iUnion] at this ⊢
        obtain ⟨t, ht, hgt⟩ := this
        exact ⟨t, ht, hg, hgt⟩
      · intro g hg
        simp only [Set.mem_iUnion] at hg
        obtain ⟨t, -, hg, -⟩ := hg
        exact hg
    rw [hcov𝓕]
    refine integrableOn_finset_iUnion.mpr fun t ht => ?_
    obtain ⟨Cφ, hCφ⟩ := AutomorphicForm.exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection K hα 1 1 hU1 hU1 s (φ s) (hφ s) (hφc s)
    obtain ⟨CE, hCE⟩ := AutomorphicForm.exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet K
      c u d₁' d₂' hc t s.re hs
    set p : ℝ := s.re + 1 / 2 with hp
    have hp0 : 0 ≤ p := by rw [hp]; linarith
    set N : ℕ := ⌈p⌉₊ with hN
    have hpN : p ≤ (N : ℝ) := Nat.le_ceil p
    set C₀ : ℝ := max Cφ 0 * max CE 0 with hC₀
    have hC₀nn : 0 ≤ C₀ := mul_nonneg (le_max_right _ _) (le_max_right _ _)
    have hdom : ∀ g ∈ 𝓕 ∩ (· * t) '' centreCutSiegelSet K c u d₁' d₂',
        ‖‖x g‖ ^ 2 * (‖φ s g‖ + ∑' ξ : K, ‖φ s (adelicWeyl (𝓞 K) K *
            unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)‖) *
          NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w)‖ ≤
        C₀ * (‖x g‖ * ‖x g‖ * (1 + archHeight K (glArch (𝓞 K) K (g * t⁻¹))) ^ N *
          NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w)) := by
      rintro g ⟨-, s₀, hs₀, rfl⟩
      obtain ⟨hsumE, hEle⟩ := hCE s₀ hs₀
      have hwt : 0 ≤ NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (s₀ * t)) ^ (-w) :=
        Real.rpow_nonneg (NumberField.TateGlobal.ideleNorm_pos _).le _
      have hCφ' : ∀ g, ‖φ s g‖ ≤ max Cφ 0 * adelicHeight K g ^ p := fun g =>
        (hCφ g).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (adelicHeight_pos g).le _))
      have hmajle : ‖φ s (s₀ * t)‖ + ∑' ξ : K, ‖φ s (adelicWeyl (𝓞 K) K *
            unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * (s₀ * t))‖ ≤
          max Cφ 0 * (adelicHeight K (s₀ * t) ^ p + ∑' ξ : K, adelicHeight K (adelicWeyl (𝓞 K) K *
            unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * (s₀ * t)) ^ p) := by
        rw [mul_add, ← tsum_mul_left]
        refine add_le_add (hCφ' _) ?_
        refine Summable.tsum_le_tsum (fun ξ => hCφ' _) (hφsum s _ hs) (hsumE.mul_left _)
      have hEle' : adelicHeight K (s₀ * t) ^ p + ∑' ξ : K, adelicHeight K (adelicWeyl (𝓞 K) K *
            unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * (s₀ * t)) ^ p ≤
          max CE 0 * (1 + archHeight K (glArch (𝓞 K) K s₀)) ^ N := by
        refine hEle.trans ?_
        have hH0 : 0 ≤ archHeight K (glArch (𝓞 K) K s₀) := (archHeight_pos K _).le
        have h1 : archHeight K (glArch (𝓞 K) K s₀) ^ p ≤ (1 + archHeight K (glArch (𝓞 K) K s₀)) ^ (N : ℝ) :=
          (Real.rpow_le_rpow hH0 (by linarith) hp0).trans
            (Real.rpow_le_rpow_of_exponent_le (by linarith) hpN)
        rw [Real.rpow_natCast] at h1
        calc CE * archHeight K (glArch (𝓞 K) K s₀) ^ p
            ≤ max CE 0 * archHeight K (glArch (𝓞 K) K s₀) ^ p :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hH0 _)
          _ ≤ max CE 0 * (1 + archHeight K (glArch (𝓞 K) K s₀)) ^ N :=
              mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
      have hmaj0 : 0 ≤ ‖φ s (s₀ * t)‖ + ∑' ξ : K, ‖φ s (adelicWeyl (𝓞 K) K *
            unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * (s₀ * t))‖ :=
        add_nonneg (norm_nonneg _) (tsum_nonneg fun _ => norm_nonneg _)
      rw [mul_inv_cancel_right, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hmaj0) hwt), sq]
      have hxx : 0 ≤ ‖x (s₀ * t)‖ * ‖x (s₀ * t)‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      calc ‖x (s₀ * t)‖ * ‖x (s₀ * t)‖ * (‖φ s (s₀ * t)‖ + ∑' ξ : K, ‖φ s (adelicWeyl (𝓞 K) K *
              unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * (s₀ * t))‖) *
            NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (s₀ * t)) ^ (-w)
          ≤ ‖x (s₀ * t)‖ * ‖x (s₀ * t)‖ * (max Cφ 0 * (max CE 0 * (1 + archHeight K (glArch (𝓞 K) K s₀)) ^ N)) *
            NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (s₀ * t)) ^ (-w) := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hxx) hwt
              exact hmajle.trans (mul_le_mul_of_nonneg_left hEle' (le_max_right _ _))
        _ = C₀ * (‖x (s₀ * t)‖ * ‖x (s₀ * t)‖ * (1 + archHeight K (glArch (𝓞 K) K s₀)) ^ N *
            NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (s₀ * t)) ^ (-w)) := by
              rw [hC₀]; ring
    have hbd := (hdecay t ht N).const_mul C₀
    have hmeasPiece : MeasurableSet (𝓕 ∩ (· * t) '' centreCutSiegelSet K c u d₁' d₂') :=
      h𝓕m.inter ((Homeomorph.mulRight t).measurableEmbedding.measurableSet_image.mpr
        (measurableSet_centreCutSiegelSet c u d₁' d₂'))
    refine Integrable.mono' hbd ?_ ?_
    ·
      have hwtc : Continuous fun g : AdelicGL2 (𝓞 K) K =>
          NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w) :=
        (NumberField.TateGlobal.continuous_ideleNorm_det K).rpow_const fun g =>
          Or.inl (NumberField.TateGlobal.ideleNorm_pos _).ne'
      exact (((hxc.norm.pow 2).measurable.mul (RS12T.measurable_majorant K (φ s) (hφc s))).mul
        hwtc.measurable).aestronglyMeasurable
    · exact (ae_restrict_iff' hmeasPiece).mpr (Filter.Eventually.of_forall hdom)
  obtain ⟨cIW, hcIW0, hcIWtop, hIW⟩ :=
    AutomorphicForm.exists_lintegral_rationalCentreUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa K
  have hDexists : ∃ D : Set (AdeleRing (𝓞 K) K)ˣ, MeasurableSet D ∧
      IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K) := by
    haveI := NumberField.Idele.isHaarMeasure_idelicHaar K
    obtain ⟨D, hD, hDF, -⟩ :=
      NumberField.TateGlobal.exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow K
        (NumberField.Idele.idelicHaar K)
    exact ⟨D, hD, hDF⟩
  obtain ⟨D, hD, hDF⟩ := hDexists
  obtain ⟨Cctr, hCctr0, hCctrtop, hCctr⟩ :=
    NumberField.Idele.exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const K D hD hDF 1 2 one_pos one_lt_two
  have hsmall := fun (g : AdelicGL2 (𝓞 K) K) (hg : glArch (𝓞 K) K g = 1) =>
    AutomorphicForm.CuspidalConstituent.exists_norm_whittakerCoefficient_diagOne_mul_le_ideleNorm_rpow_mul_prod_min_of_isCuspConstituent_mul_of_glArch_eq_one
      K c u d₁ d₂ T hc hd₁ hd hcov R.centralChar Θ.level hN tys V hV (rightConv K R.toFun f) hx₀cut w hω' g hg
  have harchT : ∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 → ∀ F : AdelicGL2 (𝓞 K) K → ℂ,
      F ∈ archCutSubmodule K tys → (fun y => F (y * g)) ∈ archCutSubmodule K tys := by
    intro g hg F hF
    rw [mem_archCutSubmodule_iff] at hF ⊢
    intro pl
    let L : (AdelicGL2 (𝓞 K) K → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 K) K → ℂ) :=
      { toFun := fun F y => F (y * g), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hle : (⨆ i : Fin (tys.card pl), archTypeSubmoduleAt K pl (tys.rep pl i)) ≤
        (⨆ i : Fin (tys.card pl), archTypeSubmoduleAt K pl (tys.rep pl i)).comap L := by
      refine iSup_le fun i => ?_
      intro G hG
      refine Submodule.mem_comap.mpr (Submodule.mem_iSup_of_mem i ?_)
      exact comp_mul_mem_typeSubmodule_of_commute hG g fun k =>
        RS27.mul_comm_of_glArch_eq_one_of_glFin_eq_one K hg (glFin_rowIsometryInclAt₀ K pl k)
    exact hle (hF pl)
  have hlarge : ∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 → ∀ M : ℕ,
      ∃ Cg : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ pl : InfinitePlace K,
          ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) 1
            (diagOne a * k * g)‖ ≤
            Cg * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)) := by
    intro g hg M
    set fg : AdelicGL2 (𝓞 K) K → ℂ := fun z => ∑ i : Fin 1, (1 : ℂ) * f ((g)⁻¹ * z) with hfg
    have hfgT : IsFactorizableTestFn K fg :=
      RS12T.isFactorizableTestFn_sum_left_translate K f hfT (fun _ : Fin 1 => g) (fun _ => hg) (fun _ => 1)
    obtain ⟨hfc, hfcs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K f hfT
    have hconvg : rightConv K R.toFun fg = fun y => rightConv K R.toFun f (y * g) := by
      funext y
      rw [hfg, RS12T.rightConv_sum_left_translate K R.toFun f hR hfc hfcs (fun _ : Fin 1 => g) (fun _ => 1) y]
      simp
    have hxtg : rightConv K R.toFun fg ∈ archCutSubmodule K tys := by
      rw [hconvg]; exact harchT g hg _ hx₀arch
    obtain ⟨Cg, hCg⟩ :=
      AutomorphicForm.exists_norm_whittakerCoefficient_rightConv_diagOne_mul_le_ideleNorm_rpow_mul_norm_infinitePlace_rpow_neg K
        c u d₁ d₂ T hd hcov R.centralChar R.toFun R.smoothCusp.1 hR fg hfgT tys hxtg w hω' M
    refine ⟨Cg, fun k hk hka a ha pl => ?_⟩
    have := hCg k hk hka a ha pl
    rwa [hconvg, ← RS12W.whittakerCoefficient_mul_right] at this
  have hx0 : ∀ g, whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 0 g = 0 := by
    intro g
    rw [whittakerCoefficient_zero_eq_constantTerm]
    exact hx1.1.2 g
  have hxleftN : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K),
      x (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = x g := by
    intro β g
    rw [RS12T.unipotentGL2_algebraMap_eq_globalPoints]
    exact hxG _ g
  have hxsmoothArch := (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn K R.toFun hR f' hf'T).2
  have hxint : ∀ (α' : K) (g : AdelicGL2 (𝓞 K) K), WhittakerCoefficientIntegrable K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
      (NumberField.StandardAddChar.stdAddChar K) x α' g :=
    (AutomorphicForm.whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace K
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) _ (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K) x hxleftN hx1.2
      hxsmoothArch).1
  have hxper : ∀ (β : K) (uu : AdeleRing (𝓞 K) K) (hh : AdelicGL2 (𝓞 K) K),
      x (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + uu) * hh) = x (unipotentGL2 uu * hh) := by
    intro β uu hh
    rw [unipotentGL2_add, mul_assoc, RS12T.unipotentGL2_algebraMap_eq_globalPoints, hxG]
  have hxW : ∀ g, Summable (fun b : K =>
      ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x b g‖) := by
    have hsmooth := (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn K R.toFun hR f' hf'T).2
    exact AutomorphicForm.summable_norm_whittakerCoefficient_of_isKfSmooth_of_contDiff_mixedSpace K
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) _ (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K) x hxleftN hx1.2 hsmooth
  have PKGx := fun (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) =>
    AutomorphicForm.SmoothCuspRealizationAt.unramified_package_rightConv_sum_translate
      K c u d₁ d₂ T Θ R hR (fun g k hk => hRlev g k hk) f hfT S Sf Sψ hSf_sub hSψ_sub hfsupp hS_good hSψ0
      r h cs hharch hhcomm x hxsum hxint hxper hxZ v hv
  have hconv := fun (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) => (PKGx v hv).1
  have hκex : ∃ κ : ℝ, ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ‖Θ.a v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
      ‖Θ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ := by
    obtain ⟨Sfd, hSs, hSfd⟩ := AutomorphicForm.exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc K 1 2
    have hpair := AutomorphicForm.exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain K
      c u d₁ d₂ T hd hcov Θ Θ R R hR w hω' 1 2 one_pos one_lt_two Sfd hSs hSfd
    obtain ⟨κ, hκ0, hκ⟩ :=
      AutomorphicForm.exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing K
        c u d₁ d₂ T Θ R w Sfd hpair (NumberField.TateGlobal.ideleNorm_uniformizerIdele K)
    refine ⟨κ, fun v _ => ⟨(hκ v).1, ?_⟩⟩
    have hN1 : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
      have h1 : 1 ≤ Ideal.absNorm v.asIdeal := Nat.one_le_iff_ne_zero.mpr (by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
      exact_mod_cast h1
    rw [norm_div, Complex.norm_natCast]
    calc ‖Θ.b v‖ / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≤ ‖Θ.b v‖ := div_le_self (norm_nonneg _) hN1
      _ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ := (hκ v).2
  have hUW : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ g : AdelicGL2 (𝓞 K) K,
      Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
        (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
             (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2 →
      (∀ m : ℕ,
        whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 ((heckeGen (𝓞 K) K v) ^ m * g) * (starRingEnd ℂ) (whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 ((heckeGen (𝓞 K) K v) ^ m * g)) =
          UnramifiedWhittaker.heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (Θ.toRawCentral.a v) (Θ.toRawCentral.b v) m *
            UnramifiedWhittaker.heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)
              ((starRingEnd ℂ) (Θ.toRawCentral.a v)) ((starRingEnd ℂ) (Θ.toRawCentral.b v)) m *
            (whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 (g) * (starRingEnd ℂ) (whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 (g)))) ∧
      (∀ m : ℕ, 0 < m → whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 ((heckeGen (𝓞 K) K v)⁻¹ ^ m * g) = 0) := by
    intro v hv g hg
    obtain ⟨ψv, ϖ, hπ, b, hgen, -, hψ0, hψ1, hNw, hKw, hTw, hZw⟩ := (PKGx v hv).2
    haveI : Nonempty (Fin (Ideal.absNorm v.asIdeal)) := by
      refine ⟨⟨0, ?_⟩⟩
      rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    have hI : Fintype.card (Fin (Ideal.absNorm v.asIdeal)) = Ideal.absNorm v.asIdeal := Fintype.card_fin _
    exact UnramifiedWhittaker.mul_conj_apply_heckeGen_pow_mul_eq_of_shell_zero K v ψv ϖ hπ hgen b hI hψ0 hψ1
      _ _ (Θ.toRawCentral.a v) (Θ.toRawCentral.b v) (Θ.toRawCentral.a v) (Θ.toRawCentral.b v)
      hNw hNw hKw hKw hTw hTw hZw hZw g hg
  have hrawb : ∀ v : HeightOneSpectrum (𝓞 K), Θ.toRawCentral.b v = Θ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) := by
    intro v
    rw [HeckeEigensystem.toRawCentral_b, div_eq_inv_mul]
    rfl
  have hrawa : ∀ v : HeightOneSpectrum (𝓞 K), Θ.toRawCentral.a v = Θ.a v := fun v => rfl
  have hPexp := fun (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) (g : AdelicGL2 (𝓞 K) K)
      (hg : Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
        (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
             (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2) (m : ℕ) => by
    have h := (hUW v hv g hg).1 m
    rw [hrawa, hrawb] at h
    exact h
  have hPnegexp := fun (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) (g : AdelicGL2 (𝓞 K) K)
      (hg : Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
        (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
             (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2) => (hUW v hv g hg).2
  have hposK : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
      (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
      0 ≤ (φ (1 / 2) k).re ∧ (φ (1 / 2) k).im = 0 := by
    intro k hk hka
    rw [hφhalf]
    rcases hφ₀val k hk hka with h0 | h1
    · rw [h0]; simp
    · rw [h1]; simp
  have hexK : ∃ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K ∧
      (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) ∧ φ (1 / 2) k ≠ 0 := by
    refine ⟨1, by rw [map_one]; exact Subgroup.one_mem _, fun pl => ?_, by rw [hφhalf, hφ₀one]; exact one_ne_zero⟩
    rw [map_one, map_one]
    exact isRowIsometry_one
  have hxKS : ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, x (g * k) = x g :=
    AutomorphicForm.apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway K S x hx1.2
      (fun v hv => (hconv v hv).1)
  have hφKS : ∀ s, ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, φ s (g * k) = φ s g := fun s =>
    AutomorphicForm.apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway K S (φ s) (hφf s)
      (fun v hv => hφsph s v hv)
  have hfin1 : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 → glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K :=
    fun k hk => by rw [hk]; exact Subgroup.one_mem _
  have hφval : ∀ (s : ℂ) (k : AdelicGL2 (𝓞 K) K), glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
      (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) → φ s k = 0 ∨ φ s k = 1 := by
    intro s k hk hka
    rw [hφflat s (1 / 2) k hk hka, hφhalf]
    exact hφ₀val k hk hka
  have hφone : ∀ (s : ℂ) (k : AdelicGL2 (𝓞 K) K), glFin (𝓞 K) K k = 1 →
      (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) → φ s k = 1 := by
    intro s k hk hka
    rw [hφflat s (1 / 2) k (hfin1 k hk) hka, hφhalf, ← one_mul k, hφ₀arch 1 k hk hka, hφ₀one]
  have hφsupp : ∀ (s : ℂ) (k : AdelicGL2 (𝓞 K) K), glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
      (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
      (∃ v ∈ S, ¬ Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
          Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
            ((Multiplicative.ofAdd (-(nS : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        φ s k = 0 := by
    intro s k hk hka hex
    rw [hφflat s (1 / 2) k hk hka, hφhalf]
    exact hφ₀supp k hex
  obtain ⟨aS, haS, -, hJan, hJpos⟩ :=
    AutomorphicForm.RankinSelberg.analyticOnNhd_sPartIntegral_and_pos_of_shell_surgery K hα
      cIW hcIW0 hcIWtop hIW S D hD hDF 1 2 one_pos one_lt_two Cctr hCctr0 hCctrtop hCctr
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) ωR w hω
      (rightConv K R.toFun f) Θ.level hN hx₀lev hsmall hlarge t₀ ht₀ k₀ hk₀ hWpt κ hκdef aexp haexp_spec
      r y cs m hysupp (fun t g' hg' => by simpa only [hx₀κdef] using hWmult t g' hg') hμbox hboxvan
      x (fun g => by rw [hxsum g]) hxc hxG (fun z g => by rw [hωR_apply]; exact hxZ z g) hxKS
      nS hnS0 hxlow φ hφ hφjc hφhol hφKS hφval hφone hφsupp
  refine ⟨S, f', φ, w, 1, 2, d₁', d₂', aS, 𝓕, tset, hS_good, hf'T, hφ, hφK, hφf, hφjc, hφhol, hφsum, hφsph, hposK, hexK,
    one_pos, one_lt_two, h𝓕m, h𝓕s, h𝓕, hd₁', h𝓕covC, hxc, hx1.2, hx1.1.2, hxG, hxZ, hω', hx0, hxW,
    fun v hv => (hconv v hv).1, fun v hv => (hconv v hv).2, hκex, hPexp, hPnegexp, hdecay, hmaj, hPne, haS, hJan, hJpos⟩

end
end S_AutomorphicForm_RankinSelberg_exists_testData_sPartIntegral_self_analyticOnNhd_re_pos
end P2MW
export P2MW.S_AutomorphicForm_RankinSelberg_exists_testData_sPartIntegral_self_analyticOnNhd_re_pos (solution)
