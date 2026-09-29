-- Prove2me | solution 1 for AutomorphicForm.RankinSelberg.exists_testData_analyticOnNhd_sub_mul_peterssonIntegral_and_hasProd_rsEulerPoly_pair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/fa056ad7-1155-5f5c-bed3-1cda7298d22b

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RankinSelbergQuotientIntegral
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.ReImTopology
import Theorems.Thm_AutomorphicForm_RankinSelberg_exists_testData_sPartIntegral_pair_analyticOnNhd_ne_zero
import Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_sub_mul_bruhatEisenstein_norm_le_archHeight_pow_of_ne_of_isArchKFinite_family
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Theorems.Thm_AutomorphicForm_RankinSelberg_exists_hasProd_quotientIntegral_eq_sPartIntegral_mul_of_shell_recursion
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow
import Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_eq_sub_mul_peterssonIntegral_of_norm_le_archHeight_pow_centreCutSiegelSet
import Theorems.Thm_AutomorphicForm_exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family
import Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family
import Theorems.Thm_AutomorphicForm_peterssonIntegral_mul_bruhatEisenstein_eq_integral_whittakerCoefficient_mul_conj_rationalCentreUnipotentQuotient
import Theorems.Thm_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Theorems.Thm_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc
import Theorems.Thm_AutomorphicForm_exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
import Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
import Theorems.Thm_AutomorphicForm_a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_RankinSelberg_exists_testData_analyticOnNhd_sub_mul_peterssonIntegral_and_hasProd_rsEulerPoly_pair
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension"
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal"
p2m_attr_erase "simp" "AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply"
p2m_attr_erase "simp" "Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec"
p2m_attr_erase "simp" "FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport"
p2m_attr_erase "simp" "RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply"

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open UnramifiedWhittaker Filter Topology NumberField.TateGlobal
open AutomorphicForm.CuspidalConstituent
open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace RS12K

variable {K : Type} [Field K] [NumberField K]

open Polynomial in

theorem rsEulerPoly_swap (A B e₁ e₂ : ℂ) :
    LanglandsTunnell.RankinSelberg.rsEulerPoly A B e₁ e₂ 0 =
      LanglandsTunnell.RankinSelberg.rsEulerPoly e₁ e₂ A B 0 := by
  simp only [LanglandsTunnell.RankinSelberg.rsEulerPoly]
  ring_nf

open Polynomial in

theorem eval_rsEulerPoly_scale (A B e₁ e₂ χ X : ℂ) :
    (LanglandsTunnell.RankinSelberg.rsEulerPoly A B (χ * e₁) (χ ^ 2 * e₂) 0).eval X =
      (LanglandsTunnell.RankinSelberg.rsEulerPoly A B e₁ e₂ 0).eval (χ * X) := by
  simp only [LanglandsTunnell.RankinSelberg.rsEulerPoly, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_sub,
    eval_neg, eval_one]
  ring

theorem cpow_sq (N p : ℂ) : (N ^ p) ^ 2 = N ^ (2 * p) := by
  rw [show (2 : ℂ) * p = ((2 : ℕ) : ℂ) * p by norm_num, Complex.cpow_nat_mul]

theorem local_factor_eq_pair (n : ℕ) (hn : 1 < n) (a b a' b' : ℂ) (w : ℝ) (s : ℂ) (hb' : b' ≠ 0)
    (hconjb : (starRingEnd ℂ) b' = ((((n : ℝ)) ^ (1 - w) : ℝ) : ℂ) ^ 2 / b')
    (hconja : (starRingEnd ℂ) a' = ((((n : ℝ)) ^ (1 - w) : ℝ) : ℂ) * (a' / b')) :
    (1 - (b / (n : ℂ)) * (starRingEnd ℂ) (b' / (n : ℂ)) *
        (((((1 : (ℂ)ˣ) : ℂ) * (n : ℂ) ^ ((1 / 2 + w : ℂ) - s)) / (n : ℂ)) ^ 2)) /
      (LanglandsTunnell.RankinSelberg.rsEulerPoly a ((n : ℂ) * (b / (n : ℂ))) ((starRingEnd ℂ) a')
          ((n : ℂ) * (starRingEnd ℂ) (b' / (n : ℂ))) 0).eval
        ((((1 : (ℂ)ˣ) : ℂ) * (n : ℂ) ^ ((1 / 2 + w : ℂ) - s)) / (n : ℂ) ^ 2) =
    (1 - b * (starRingEnd ℂ) b' * (n : ℂ) ^ ((2 * w - 2 : ℂ)) * (n : ℂ) ^ (-(2 * s + 1))) *
      ((LanglandsTunnell.RankinSelberg.rsEulerPoly (a' / b') b'⁻¹ a b 0).eval ((n : ℂ) ^ (-(s + 1 / 2))))⁻¹ := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hnr : (0 : ℝ) ≤ (n : ℝ) := by positivity
  set N : ℂ := (n : ℂ) with hN
  set χ : ℂ := ((((n : ℝ)) ^ (1 - w) : ℝ) : ℂ) with hχdef
  have hχ : χ = N ^ (((1 - w : ℝ)) : ℂ) := by
    rw [hχdef, Complex.ofReal_cpow hnr]; push_cast; rfl
  have hconjN : (starRingEnd ℂ) N = N := by rw [hN]; exact Complex.conj_natCast n
  have hconjbN : (starRingEnd ℂ) (b' / N) = (starRingEnd ℂ) b' / N := by rw [map_div₀, hconjN]
  simp only [Units.val_one, one_mul]
  rw [hconjbN, mul_div_cancel₀ _ hn0, mul_div_cancel₀ _ hn0, hconja, hconjb, div_eq_mul_inv (χ ^ 2) b',
    RS12K.eval_rsEulerPoly_scale, RS12K.rsEulerPoly_swap]
  have hy1 : χ * (N ^ ((1 / 2 + w : ℂ) - s) / N ^ 2) = N ^ (-(s + 1 / 2)) := by
    rw [hχ, show (N ^ 2 : ℂ) = N ^ ((2 : ℕ) : ℂ) by rw [Complex.cpow_natCast],
      div_eq_mul_inv, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hn0, ← Complex.cpow_add _ _ hn0]
    congr 1; push_cast; (try ring)
  rw [hy1]

  have hy2 : (N ^ ((1 / 2 + w : ℂ) - s)) ^ 2 / N ^ 4 = N ^ ((2 * w - 2 : ℂ)) * N ^ (-(2 * s + 1)) := by
    rw [cpow_sq, show (N ^ 4 : ℂ) = N ^ ((4 : ℕ) : ℂ) by rw [Complex.cpow_natCast],
      div_eq_mul_inv, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hn0, ← Complex.cpow_add _ _ hn0]
    congr 1; push_cast; ring
  have hnum : 1 - b / N * (χ ^ 2 * b'⁻¹ / N) * (N ^ ((1 / 2 + w : ℂ) - s) / N) ^ 2 =
      1 - b * (χ ^ 2 * b'⁻¹) * N ^ ((2 * w - 2 : ℂ)) * N ^ (-(2 * s + 1)) := by
    have h3 : b / N * (χ ^ 2 * b'⁻¹ / N) * (N ^ ((1 / 2 + w : ℂ) - s) / N) ^ 2 =
        b * (χ ^ 2 * b'⁻¹) * ((N ^ ((1 / 2 + w : ℂ) - s)) ^ 2 / N ^ 4) := by
      field_simp
    rw [h3, hy2]
    ring
  rw [hnum]
  try rw [div_eq_mul_inv]

end RS12K

theorem solution
    (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
      (_hc : 0 < c) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
      (_hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
      (σ τ : HeckeEigensystem K ℂ)
      (Rσ : SmoothCuspRealizationAt K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) σ.toRawCentral)
      (_hRσ : IsGenuineCuspRealizationAt K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) σ.toRawCentral Rσ)
      (Rτ : SmoothCuspRealizationAt K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) τ.toRawCentral)
      (_hRτ : IsGenuineCuspRealizationAt K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) τ.toRawCentral Rτ)
      (tysσ : AutomorphicForm.ArchTypeFamily K)
      (Vσ : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
      (_hVσ : IsCuspConstituent K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Rσ.centralChar Vσ)
      (_hRσV : Rσ.toFun ∈ Vσ ⊓ levelInvariantSubmodule K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) σ.level ⊓ archCutSubmodule K tysσ)
      (tysτ : AutomorphicForm.ArchTypeFamily K)
      (Vτ : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
      (_hVτ : IsCuspConstituent K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Rτ.centralChar Vτ)
      (_hRτV : Rτ.toFun ∈ Vτ ⊓ levelInvariantSubmodule K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) τ.level ⊓ archCutSubmodule K tysτ)
      (_hw : ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)), ∀ v ∉ S₀, ‖σ.b v‖ = ‖τ.b v‖),
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (fx fy : AdelicGL2 (𝓞 K) K → ℂ)
      (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (w e₁ e₂ a σ₀ : ℝ) (s₀ C : ℂ) (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (A L ζi : ℂ → ℂ),
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ¬ v.asIdeal ∣ σ.level ∧ ¬ v.asIdeal ∣ τ.level ∧ v ∉ Rσ.exceptionalSet ∧ v ∉ Rτ.exceptionalSet) ∧
      IsFactorizableTestFn K fx ∧ IsFactorizableTestFn K fy ∧
      IsUnitaryChar (𝓞 K) K ν ∧ IsIdeleClassChar (𝓞 K) K ν ∧
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((Rτ.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (starRingEnd ℂ) ((Rσ.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) =
          ((ideleNorm K z ^ (2 * w) : ℝ) : ℂ)) ∧
      (∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((Rσ.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ideleNorm K z ^ w) ∧
      (∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((Rτ.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ideleNorm K z ^ w) ∧
      (∀ s, IsInducedSection (𝓞 K) K (etaFst 1 α hα s) (etaSnd ν α hα s) (φ s)) ∧
      (∀ s, IsArchKFinite K (φ s)) ∧ (∀ s, IsKfSmooth K (φ s)) ∧
      Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φ p.1 p.2) ∧
      (∀ g, Differentiable ℂ (fun s => φ s g)) ∧
      0 < e₁ ∧ e₁ < e₂ ∧
      𝓕 ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂} ∧
      IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
          {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}) ∧
      a < 1 / 2 ∧ 1 / 2 < σ₀ ∧ C ≠ 0 ∧

      AnalyticOnNhd ℂ A {s : ℂ | a < s.re} ∧
      (∀ s : ℂ, 1 / 2 < s.re → A s = (s - s₀) * peterssonIntegral K w 𝓕
          (fun g => rightConv K Rτ.toFun fx g * (φ s g + ∑' ξ : K, φ s (adelicWeyl (𝓞 K) K *
            unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g))) (rightConv K Rσ.toFun fy)) ∧

      (ν ≠ 1 → s₀ ≠ 1 / 2) ∧
      (ν = 1 → s₀ = 1 / 2 ∧ Rτ.centralChar = Rσ.centralChar ∧
        (A (1 / 2) ≠ 0 → ∃ g₁ g₂ : AdelicGL2 (𝓞 K) K,
          peterssonIntegral K w 𝓕 (fun h => Rτ.toFun (h * g₁)) (fun h => Rσ.toFun (h * g₂)) ≠ 0)) ∧

      AnalyticOnNhd ℂ (fun s : ℂ => RankinSelberg.sPartIntegral K S
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (rightConv K Rτ.toFun fx) (rightConv K Rσ.toFun fy) (φ s) w e₁ e₂) {s : ℂ | a < s.re} ∧
      RankinSelberg.sPartIntegral K S
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (rightConv K Rτ.toFun fx) (rightConv K Rσ.toFun fy) (φ (1 / 2)) w e₁ e₂ ≠ 0 ∧

      AnalyticOnNhd ℂ ζi {s : ℂ | a < s.re} ∧
      (∀ s : ℂ, a < s.re → ζi s ≠ 0 ∧
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
          (1 - τ.b v.1 * (starRingEnd ℂ) (σ.b v.1) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((2 * w - 2 : ℂ)) *
            ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) (ζi s)) ∧

      AnalyticOnNhd ℂ L {s : ℂ | σ₀ < s.re} ∧
      (∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (σ.a v.1 / σ.b v.1) (σ.b v.1)⁻¹
              (τ.a v.1) (τ.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(s + 1 / 2))))⁻¹) (L s) ∧
        peterssonIntegral K w 𝓕
          (fun g => rightConv K Rτ.toFun fx g * (φ s g + ∑' ξ : K, φ s (adelicWeyl (𝓞 K) K *
            unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g))) (rightConv K Rσ.toFun fy) =
        C * RankinSelberg.sPartIntegral K S
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (rightConv K Rτ.toFun fx) (rightConv K Rσ.toFun fy) (φ s) w e₁ e₂ * ζi s * L s) := by
  intro α hα c u d₁ d₂ T hc hd₁ hd hcov σ τ Rσ hRσ Rτ hRτ tysσ Vσ hVσ hRσV tysτ Vτ hVτ hRτV hw
  obtain ⟨S, fx, fy, ν, φ, w, e₁, e₂, d₁', d₂', aT, 𝓕, tset, hS, hfx, hfy, hνu, hνF, hZtot, hφ, hφK, hφf, hφjc, hφhol,
    hφsum, hφsph, hposν, he₁, he, h𝓕m, h𝓕s, h𝓕, hd₁', h𝓕cov,
    hxc, hxKf, hxcusp, hxG, hxZ, hωτ, hx0, hxW, hxK, hxHecke, hxneg, hxdecay, hxmaj,
    hyc, hyKf, hycusp, hyG, hyZ, hωσ, hy0, hyW, hyK, hyHecke, hyneg, hydecay, hymaj,
    hdecay, hF1, hF2, ⟨κ, hκ⟩, hP, haT, hJan, hJ0⟩ :=
    AutomorphicForm.RankinSelberg.exists_testData_sPartIntegral_pair_analyticOnNhd_ne_zero K hα c u d₁ d₂ T hc hd₁ hd hcov
      σ τ Rσ hRσ Rτ hRτ tysσ Vσ hVσ hRσV tysτ Vτ hVτ hRτV hw
  set ψ := NumberField.StandardAddChar.stdAddChar K with hψdef
  set x : AdelicGL2 (𝓞 K) K → ℂ := rightConv K Rτ.toFun fx with hxdef
  set y : AdelicGL2 (𝓞 K) K → ℂ := rightConv K Rσ.toFun fy with hydef
  have hψ : IsGlobalAddChar K ψ := NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K
  have hφc : ∀ s, Continuous (φ s) := fun s =>
    hφjc.comp (Continuous.prodMk continuous_const continuous_id)

  have hN : ∀ v : HeightOneSpectrum (𝓞 K), (1 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    intro v
    have h1 : 1 < Ideal.absNorm v.asIdeal := by
      rw [Nat.one_lt_iff_ne_zero_and_ne_one]
      exact ⟨by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot,
        by rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top⟩
    exact_mod_cast h1
  have hN0 : ∀ v : HeightOneSpectrum (𝓞 K), (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := fun v =>
    lt_trans zero_lt_one (hN v)
  have hNC : ∀ v : HeightOneSpectrum (𝓞 K), (((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) ≠ 0 := fun v => by
    exact_mod_cast (hN0 v).ne'

  have bridge : ∀ (Θ : HeckeEigensystem K ℂ) (R : SmoothCuspRealizationAt K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral)
      (hR : IsGenuineCuspRealizationAt K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral R)
      (hω : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((R.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ideleNorm K z ^ w),
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ R.exceptionalSet → ¬ v.asIdeal ∣ Θ.level →
        Θ.a v * (starRingEnd ℂ) (Θ.b v) = ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (1 - w) : ℝ) : ℂ) * (starRingEnd ℂ) (Θ.a v) ∧
        ‖Θ.b v‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (1 - w) := by
    intro Θ R hR hω
    obtain ⟨Sfd, hSs, hSfd⟩ := AutomorphicForm.exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc K 1 2
    obtain ⟨-, hne, hcross⟩ := AutomorphicForm.exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain K c u d₁ d₂ T hd hcov Θ Θ R R hR w hω 1 2 one_pos one_lt_two Sfd hSs hSfd
    obtain ⟨-, P, hPcov, -, hPagree⟩ := hcross rfl
    have hRmem : R.toFun ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 K) K => fun z => R.toFun (z * h)) :=
      Submodule.subset_span ⟨1, funext fun z => by simp⟩
    have hPcov' : ∀ g : AdelicGL2 (𝓞 K) K, ∀ x y : AdelicGL2 (𝓞 K) K → ℂ,
        x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 K) K => fun z => R.toFun (z * h)) →
        y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 K) K => fun z => R.toFun (z * h)) →
        P (fun z => x (z * g)) (fun z => y (z * g)) =
          ((ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ w : ℝ) : ℂ) * P x y :=
      fun g x y hx hy => hPcov g x y (Submodule.mem_sup_left hx) hy
    have hPself : P R.toFun R.toFun ≠ 0 := by
      rw [hPagree R.toFun R.toFun (Submodule.mem_sup_left hRmem) hRmem]; exact hne
    exact AutomorphicForm.a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) Θ R P w hPcov' hPself
  have hgoodσ : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      σ.b v ≠ 0 ∧ ‖σ.b v‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (1 - w) ∧
      (starRingEnd ℂ) (σ.b v) = ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (1 - w) : ℝ) : ℂ) ^ 2 / σ.b v ∧
      (starRingEnd ℂ) (σ.a v) = ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (1 - w) : ℝ) : ℂ) * (σ.a v / σ.b v) := by
    intro v hv
    obtain ⟨hlσ, -, heσ, -⟩ := hS v hv
    obtain ⟨hab, hbn⟩ := bridge σ Rσ hRσ hωσ v heσ hlσ
    have hbpos : 0 < ‖σ.b v‖ := by rw [hbn]; exact Real.rpow_pos_of_pos (hN0 v) _
    have hb0 : σ.b v ≠ 0 := norm_pos_iff.mp hbpos
    set χ : ℂ := ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (1 - w) : ℝ) : ℂ) with hχ
    have hconjb : (starRingEnd ℂ) (σ.b v) = χ ^ 2 / σ.b v := by
      rw [eq_div_iff hb0, Complex.conj_mul', hbn]
    refine ⟨hb0, hbn, hconjb, ?_⟩
    have hχ0 : χ ≠ 0 := by
      rw [hχ]; exact_mod_cast (Real.rpow_pos_of_pos (hN0 v) _).ne'
    have h1 : σ.a v * (χ ^ 2 / σ.b v) = χ * (starRingEnd ℂ) (σ.a v) := by rw [← hconjb]; exact hab
    field_simp at h1
    field_simp
    linear_combination (-1 : ℂ) * h1
  have hgoodτ : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      τ.b v ≠ 0 ∧ ‖τ.b v‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (1 - w) := by
    intro v hv
    obtain ⟨-, hlτ, -, heτ⟩ := hS v hv
    obtain ⟨-, hbn⟩ := bridge τ Rτ hRτ hωτ v heτ hlτ
    have hbpos : 0 < ‖τ.b v‖ := by rw [hbn]; exact Real.rpow_pos_of_pos (hN0 v) _
    exact ⟨norm_pos_iff.mp hbpos, hbn⟩

  set cv : HeightOneSpectrum (𝓞 K) → ℂ := fun v =>
      τ.b v * (starRingEnd ℂ) (σ.b v) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ ((2 * w - 2 : ℂ)) with hcv
  have hcv1 : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ‖cv v‖ = 1 := by
    intro v hv
    obtain ⟨-, hbσ, -, -⟩ := hgoodσ v hv
    have hbτ := (hgoodτ v hv).2
    simp only [hcv, norm_mul, Complex.norm_conj, hbσ, hbτ]
    rw [show (((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) = ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ)) : ℂ) by push_cast; rfl,
      show ((2 * w - 2 : ℂ)) = (((2 * w - 2 : ℝ)) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow (hN0 v).le,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (hN0 v) _),
      ← Real.rpow_add (hN0 v), ← Real.rpow_add (hN0 v)]
    rw [show (1 - w + (1 - w) + (2 * w - 2)) = (0 : ℝ) by ring, Real.rpow_zero]
  have hcvle : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, ‖cv v.1‖ ≤ 1 := fun v => (hcv1 v.1 v.2).le
  obtain ⟨hZM, hZD, hZne⟩ :=
    NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one K S (fun v => cv v.1) hcvle
  set Tz : ℂ → ℂ := fun w' => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
      (1 - cv v.1 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w'))⁻¹ with hTz
  set ζi : ℂ → ℂ := fun s => (Tz (2 * s + 1))⁻¹ with hζi
  have h2s1 : ∀ s : ℂ, 0 < s.re → 1 < (2 * s + 1).re := by
    intro s hs; simp; linarith
  have hζne : ∀ s : ℂ, 0 < s.re → ζi s ≠ 0 := fun s hs =>
    inv_ne_zero (hZne (2 * s + 1) (h2s1 s hs))
  have hζprod : ∀ s : ℂ, 0 < s.re →
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
        (1 - τ.b v.1 * (starRingEnd ℂ) (σ.b v.1) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((2 * w - 2 : ℂ)) *
            ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) (ζi s) := by
    intro s hs
    have hT : HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
        (1 - cv v.1 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))⁻¹) (Tz (2 * s + 1)) :=
      (hZM (2 * s + 1) (h2s1 s hs)).hasProd

    rw [HasProd] at hT ⊢
    refine (hT.inv₀ (hZne _ (h2s1 s hs))).congr' (Filter.Eventually.of_forall fun F => ?_)
    simp only [Finset.prod_inv_distrib, inv_inv, hcv]
  have hζdiff : DifferentiableOn ℂ ζi {s : ℂ | 0 < s.re} := by
    have hmaps : Set.MapsTo (fun s : ℂ => 2 * s + 1) {s : ℂ | 0 < s.re} {s : ℂ | 1 < s.re} :=
      fun s hs => h2s1 s hs
    have hcomp : DifferentiableOn ℂ (fun s : ℂ => Tz (2 * s + 1)) {s : ℂ | 0 < s.re} :=
      hZD.comp ((differentiable_id.const_mul (2 : ℂ)).add_const 1).differentiableOn hmaps
    exact hcomp.inv fun s hs => hZne _ (h2s1 s hs)
  have hζan0 : AnalyticOnNhd ℂ ζi {s : ℂ | 0 < s.re} :=
    hζdiff.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

  set κ' : ℝ := |κ| + |w| + 1 with hκ'
  have hκ'bd : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
      ‖σ.a v.1 / σ.b v.1‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ' ∧
      ‖(σ.b v.1)⁻¹‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ' ∧
      ‖τ.a v.1‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ' ∧
      ‖τ.b v.1‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ' := by
    intro v
    obtain ⟨hb0, hbn, -, -⟩ := hgoodσ v.1 v.2
    obtain ⟨-, hbnτ⟩ := hgoodτ v.1 v.2
    obtain ⟨haτ, -, haσ, -⟩ := hκ v.1 v.2
    have hN1 := (hN v.1).le
    have mono : ∀ p q : ℝ, p ≤ q → ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ p ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ q :=
      fun p q hpq => Real.rpow_le_rpow_of_exponent_le hN1 hpq
    have hκabs : κ ≤ κ' := by rw [hκ']; linarith [le_abs_self κ, abs_nonneg w]
    have h1w : 1 - w ≤ κ' := by rw [hκ']; linarith [abs_nonneg κ, neg_abs_le w]
    have hw1 : w - 1 ≤ κ' := by rw [hκ']; linarith [abs_nonneg κ, le_abs_self w]
    refine ⟨?_, ?_, haτ.trans (mono _ _ hκabs), by rw [hbnτ]; exact mono _ _ h1w⟩
    · rw [norm_div, hbn, div_eq_mul_inv, ← Real.rpow_neg (hN0 v.1).le]
      calc ‖σ.a v.1‖ * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-(1 - w))
          ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-(1 - w)) :=
            mul_le_mul_of_nonneg_right haσ (Real.rpow_nonneg (hN0 v.1).le _)
        _ = ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (κ + -(1 - w)) := by rw [Real.rpow_add (hN0 v.1)]
        _ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ' := mono _ _ (by rw [hκ']; linarith [le_abs_self κ, le_abs_self w])
    · rw [norm_inv, hbn, ← Real.rpow_neg (hN0 v.1).le]
      exact mono _ _ (by linarith [hw1])
  obtain ⟨σA, hLM, hLD, hLne⟩ := LanglandsTunnell.RankinSelberg.exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow K S
    (fun v => σ.a v.1 / σ.b v.1) (fun v => (σ.b v.1)⁻¹) (fun v => τ.a v.1) (fun v => τ.b v.1) κ' hκ'bd
  set L : ℂ → ℂ := fun s => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
      ((LanglandsTunnell.RankinSelberg.rsEulerPoly (σ.a v.1 / σ.b v.1) (σ.b v.1)⁻¹ (τ.a v.1) (τ.b v.1) 0).eval
        (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(s + 1 / 2))))⁻¹ with hL
  have hLprod : ∀ s : ℂ, σA < (s + 1 / 2).re →
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
        ((LanglandsTunnell.RankinSelberg.rsEulerPoly (σ.a v.1 / σ.b v.1) (σ.b v.1)⁻¹ (τ.a v.1) (τ.b v.1) 0).eval
          (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(s + 1 / 2))))⁻¹) (L s) :=
    fun s hs => (hLM (s + 1 / 2) hs).hasProd
  have hLdiff : DifferentiableOn ℂ L {s : ℂ | σA - 1 / 2 < s.re} := by
    have hmaps : Set.MapsTo (fun s : ℂ => s + 1 / 2) {s : ℂ | σA - 1 / 2 < s.re} {s : ℂ | σA < s.re} := by
      intro s hs; show σA < (s + 1 / 2).re; simp at hs ⊢; linarith
    exact hLD.comp (differentiable_id.add_const _).differentiableOn hmaps
  have hLan : AnalyticOnNhd ℂ L {s : ℂ | σA - 1 / 2 < s.re} :=
    hLdiff.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

  have hU1 : IsUnitaryChar (𝓞 K) K (1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := fun t => by simp
  have hI1 : IsIdeleClassChar (𝓞 K) K (1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := fun t => by simp
  set ωτ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := Rτ.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom with hωτdef
  set ωσ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := Rσ.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom with hωσdef
  have hωτ_apply : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ωτ z = Rτ.centralChar ⟨z, Subgroup.mem_top z⟩ := fun z => rfl
  have hωσ_apply : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ωσ z = Rσ.centralChar ⟨z, Subgroup.mem_top z⟩ := fun z => rfl
  have hxZ' : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x (centralScalar (𝓞 K) K z * g) = ((ωτ z : ℂˣ) : ℂ) * x g := fun z g => by rw [hωτ_apply]; exact hxZ z g
  have hyZ' : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      y (centralScalar (𝓞 K) K z * g) = ((ωσ z : ℂˣ) : ℂ) * y g := fun z g => by rw [hωσ_apply]; exact hyZ z g
  have hZtot' : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ((ωτ z : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ωσ z : ℂˣ) : ℂ) * (((1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) z : ℂˣ) : ℂ) *
        ((ν z : ℂˣ) : ℂ) = ((ideleNorm K z ^ (2 * w) : ℝ) : ℂ) := by
    intro z
    simp only [MonoidHom.one_apply, Units.val_one, mul_one]
    rw [hωτ_apply, hωσ_apply]
    exact hZtot z
  have hbd4 : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ‖τ.a v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
      ‖τ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
      ‖(starRingEnd ℂ) (σ.a v)‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
      ‖(starRingEnd ℂ) (σ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ))‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ := by
    intro v hv
    obtain ⟨h1, h2, h3, h4⟩ := hκ v hv
    exact ⟨h1, h2, by rwa [Complex.norm_conj], by rwa [Complex.norm_conj]⟩
  have hPneg' : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ g : AdelicGL2 (𝓞 K) K,
      Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
        (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
             (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2 →
      ∀ m : ℕ, 0 < m →
        whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ψ x 1 ((heckeGen (𝓞 K) K v)⁻¹ ^ m * g) *
          (starRingEnd ℂ) (whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ψ y 1 ((heckeGen (𝓞 K) K v)⁻¹ ^ m * g)) = 0 := by
    intro v hv g hg m hm
    rw [hxneg v hv g hg m hm, zero_mul]
  obtain ⟨σE, hEuler⟩ := AutomorphicForm.RankinSelberg.exists_hasProd_quotientIntegral_eq_sPartIntegral_mul_of_shell_recursion K hα
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
    (fun v => heckeGen (𝓞 K) K v) ψ hψ 1 ν ωτ ωσ w hU1 hνu hZtot' hI1 hνF x y hxG hyG hxc hyc hxZ' hyZ' S hxK hyK
    (fun v => τ.a v) (fun v => τ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ))
    (fun v => (starRingEnd ℂ) (σ.a v)) (fun v => (starRingEnd ℂ) (σ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)))
    κ hbd4 hP hPneg'

  set σ₀ : ℝ := max (max σA σE) 1 with hσ₀
  have hmain : ∀ s : ℂ, σ₀ < s.re →
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
        ((LanglandsTunnell.RankinSelberg.rsEulerPoly (σ.a v.1 / σ.b v.1) (σ.b v.1)⁻¹ (τ.a v.1) (τ.b v.1) 0).eval
          (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(s + 1 / 2))))⁻¹) (L s) ∧
      peterssonIntegral K w 𝓕
          (fun g => x g * (φ s g + ∑' ξ : K, φ s (adelicWeyl (𝓞 K) K *
            unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g))) y =
        (1 : ℂ) * RankinSelberg.sPartIntegral K S (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ψ x y (φ s) w e₁ e₂ * ζi s * L s := by
    intro s hs
    have hsA : σA < (s + 1 / 2).re := by
      have : (s + 1 / 2 : ℂ).re = s.re + 1 / 2 := by simp
      rw [this]; linarith [le_max_left (max σA σE) 1, le_max_left σA σE]
    have hsE : σE < s.re := by linarith [le_max_left (max σA σE) 1, le_max_right σA σE]
    have hs1 : 1 / 2 < s.re := by linarith [le_max_right (max σA σE) 1]
    have hs0 : 0 < s.re := by linarith

    obtain ⟨hInt, hIeq⟩ := AutomorphicForm.peterssonIntegral_mul_bruhatEisenstein_eq_integral_whittakerCoefficient_mul_conj_rationalCentreUnipotentQuotient K hα
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) ψ hψ 1 ν hU1 hνu hI1 hνF s (φ s) (hφ s) (hφc s) (fun g => hφsum s g hs1)
      x y hxG hyG hxc hyc hx0 hxW w e₁ e₂ he₁ he 𝓕 h𝓕s h𝓕 (hxmaj s hs1) (hymaj s hs1)
    have hInt' : Integrable (fun q : RationalCentreUnipotentQuotient K =>
        RankinSelberg.quotientIntegrand K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ψ x y (φ s) w e₁ e₂ q.out)
        (rationalCentreUnipotentQuotientMeasure K) := hInt
    obtain ⟨Prod, hPf, hQ⟩ := hEuler s hsE (φ s) (hφ s) (hφc s) (fun v hv kv g => hφsph s v hv kv g) e₁ e₂ hInt'

    have hfac : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        (1 - (τ.b v.1 / ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ)) *
              (starRingEnd ℂ) (σ.b v.1 / ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ)) *
            (((((1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
                ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 / 2 + w : ℂ) - s)) /
              ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ)) ^ 2) /
          (LanglandsTunnell.RankinSelberg.rsEulerPoly (τ.a v.1) (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) * (τ.b v.1 / ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ)))
              ((starRingEnd ℂ) (σ.a v.1)) (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) * (starRingEnd ℂ) (σ.b v.1 / ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ))) 0).eval
            ((((((1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
                ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 / 2 + w : ℂ) - s)) /
              ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ 2)) =
        (1 - τ.b v.1 * (starRingEnd ℂ) (σ.b v.1) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((2 * w - 2 : ℂ)) *
            ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) *
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (σ.a v.1 / σ.b v.1) (σ.b v.1)⁻¹ (τ.a v.1) (τ.b v.1) 0).eval
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(s + 1 / 2))))⁻¹ := by
      intro v
      obtain ⟨hb0, -, hcb, hca⟩ := hgoodσ v.1 v.2
      have hn1 : 1 < Ideal.absNorm v.1.asIdeal := by exact_mod_cast hN v.1
      rw [MonoidHom.one_apply]
      exact RS12K.local_factor_eq_pair _ hn1 (τ.a v.1) (τ.b v.1) (σ.a v.1) (σ.b v.1) w s hb0 hcb hca
    have hPf' : HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
        (1 - τ.b v.1 * (starRingEnd ℂ) (σ.b v.1) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((2 * w - 2 : ℂ)) *
            ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) *
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (σ.a v.1 / σ.b v.1) (σ.b v.1)⁻¹ (τ.a v.1) (τ.b v.1) 0).eval
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(s + 1 / 2))))⁻¹) Prod := by
      convert hPf using 1
      funext v
      exact (hfac v).symm
    have hboth := (hζprod s hs0).mul (hLprod s hsA)
    have hProd : Prod = ζi s * L s := hPf'.unique hboth
    refine ⟨hLprod s hsA, ?_⟩
    rw [hIeq]
    show RankinSelberg.quotientIntegral K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ψ x y (φ s) w e₁ e₂ = _
    rw [hQ, hProd]
    ring

  have hσ₀' : 1 / 2 < σ₀ := by linarith [le_max_right (max σA σE) 1]
  have hLan' : AnalyticOnNhd ℂ L {s : ℂ | σ₀ < s.re} := hLan.mono (by
    intro s hs
    show σA - 1 / 2 < s.re
    have : σ₀ < s.re := hs
    linarith [le_max_left (max σA σE) 1, le_max_left σA σE])

  have h𝓕cov' : 𝓕 ⊆ ⋃ i : ↥tset, (· * (i : AdelicGL2 (𝓞 K) K)) '' centreCutSiegelSet K c u d₁' d₂' := by
    intro g hg
    have := h𝓕cov hg
    simp only [Set.mem_iUnion] at this ⊢
    obtain ⟨t, ht, hgt⟩ := this
    exact ⟨⟨t, ht⟩, hgt⟩

  have CONT : ∀ (aB : ℝ) (s₀ : ℂ) (G : ℂ → AdelicGL2 (𝓞 K) K → ℂ),
      (∀ g, AnalyticOnNhd ℂ (fun s => G s g) {s : ℂ | aB < s.re}) →
      (∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K), 1 / 2 < s.re →
        G s g = (s - s₀) * (φ s g + ∑' ξ : K, φ s (adelicWeyl (𝓞 K) K *
          unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g))) →
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => G p.1 p.2) ({s : ℂ | aB < s.re} ×ˢ Set.univ) →
      (∀ (c' u'' : ℝ) (t : AdelicGL2 (𝓞 K) K) (C : Set ℂ), 0 < c' → IsCompact C → C ⊆ {s : ℂ | aB < s.re} →
        ∃ (M : ℝ) (N : ℕ), ∀ s ∈ C, ∀ g ∈ integralWindowedSiegelSet K c' u'',
          ‖G s (g * t)‖ ≤ M * (1 + archHeight K (glArch (𝓞 K) K g)) ^ N) →
      ∀ a : ℝ, aB ≤ a → a < 1 / 2 →
        AnalyticOnNhd ℂ (fun s : ℂ => ∫ g in 𝓕, x g * G s g * (starRingEnd ℂ) (y g) *
            ((ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))
          {s : ℂ | a < s.re} ∧
        ∀ s : ℂ, 1 / 2 < s.re →
          (∫ g in 𝓕, x g * G s g * (starRingEnd ℂ) (y g) *
            ((ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
          (s - s₀) * peterssonIntegral K w 𝓕
            (fun g => x g * (φ s g + ∑' ξ : K, φ s (adelicWeyl (𝓞 K) K *
              unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g))) y := by
    intro aB s₀ G hGan hGeq hGc hGbd a haB ha
    have hsubB : {s : ℂ | a < s.re} ⊆ {s : ℂ | aB < s.re} := fun s hs => lt_of_le_of_lt haB hs

    have hGbdC : ∀ (C : Set ℂ), IsCompact C → C ⊆ {s : ℂ | a < s.re} → ∀ i : ↥tset,
        ∃ (M : ℝ) (N : ℕ), ∀ s ∈ C, ∀ g ∈ centreCutSiegelSet K c u d₁' d₂',
          ‖G s (g * (i : AdelicGL2 (𝓞 K) K))‖ ≤ M * (1 + archHeight K (glArch (𝓞 K) K g)) ^ N := by
      intro C hC hCsub i
      obtain ⟨M, N, hMN⟩ := hGbd (c ^ (∑ w : InfinitePlace K, w.mult)) u (i : AdelicGL2 (𝓞 K) K) C (pow_pos hc _) hC (hCsub.trans hsubB)
      exact ⟨M, N, fun s hs g hg => hMN s hs g (centreCutSiegelSet_subset_integralWindowedSiegelSet hc.le hg)⟩
    obtain ⟨hAan, hAeq⟩ := AutomorphicForm.exists_analyticOnNhd_eq_sub_mul_peterssonIntegral_of_norm_le_archHeight_pow_centreCutSiegelSet K w a c u d₁' d₂' hc (↥tset) (fun i => (i : AdelicGL2 (𝓞 K) K))
      𝓕 h𝓕m h𝓕cov' G (fun g => (hGan g).mono hsubB) (hGc.mono (Set.prod_mono hsubB subset_rfl)) hGbdC
      x y hxc hyc (fun i N => hdecay i.1 i.2 N)
    refine ⟨hAan, fun s hs => ?_⟩
    exact hAeq s₀ (1 / 2) (fun s g => φ s g + ∑' ξ : K, φ s (adelicWeyl (𝓞 K) K *
      unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) (fun s g hs' => hGeq s g hs') s hs (lt_of_lt_of_le ha (le_of_lt hs) |> fun h => by linarith)
  by_cases hν1 : ν = 1
  ·
    subst hν1
    obtain ⟨hpos, hex⟩ := hposν rfl
    obtain ⟨aB, G, haB, hGan, hGeq, hGc, hGbd⟩ := AutomorphicForm.exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family K hα φ hφ hφK hφf hφjc hφhol
    obtain ⟨r, aM, haM, hM2, hcrit⟩ := AutomorphicForm.exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family K hα φ hφ hφK hφf hφjc hφhol
    have hr : r ≠ 0 := hcrit hpos hex
    set a : ℝ := max (max aT (max aB aM)) (1 / 4) with ha_def
    have ha : a < 1 / 2 := by
      rw [ha_def]
      exact max_lt (max_lt haT (max_lt haB haM)) (by norm_num)
    have haT' : aT ≤ a := le_trans (le_max_left _ _) (le_max_left _ _)
    have haB' : aB ≤ a := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
    have ha0 : (0 : ℝ) < a := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hsubT : {s : ℂ | a < s.re} ⊆ {s : ℂ | aT < s.re} := fun s hs => lt_of_le_of_lt haT' hs
    have hsub0 : {s : ℂ | a < s.re} ⊆ {s : ℂ | 0 < s.re} := fun s hs => lt_trans ha0 hs
    obtain ⟨hAan, hA2⟩ := CONT aB (1 / 2) G hGan hGeq hGc hGbd a haB' ha
    set A : ℂ → ℂ := fun s : ℂ => ∫ g in 𝓕, x g * G s g * (starRingEnd ℂ) (y g) *
        ((ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) with hA_def

    have hhalf : (𝓝[{s : ℂ | 1 / 2 < s.re}] (1 / 2 : ℂ)).NeBot := by
      apply mem_closure_iff_nhdsWithin_neBot.mp
      rw [Complex.closure_setOf_lt_re]
      show (1 / 2 : ℝ) ≤ (1 / 2 : ℂ).re
      norm_num
    have hG12 : ∀ g : AdelicGL2 (𝓞 K) K, G (1 / 2) g = r := by
      intro g
      have h12B : (1 / 2 : ℂ) ∈ {s : ℂ | aB < s.re} := by show aB < (1 / 2 : ℂ).re; norm_num; linarith
      have hT1 : Tendsto (fun s => G s g) (𝓝[{s : ℂ | 1 / 2 < s.re}] (1 / 2)) (𝓝 (G (1 / 2) g)) :=
        ((hGan g (1 / 2) h12B).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
      obtain ⟨E', -, -, hE'eq, hE't⟩ := hM2 g
      have hsub : {s : ℂ | 1 / 2 < s.re} ⊆ {(1 / 2 : ℂ)}ᶜ := by
        intro s hs h
        rw [Set.mem_singleton_iff] at h
        rw [h] at hs
        norm_num at hs
      have hT2' : Tendsto (fun s : ℂ => (s - 1 / 2) * E' s) (𝓝[{s : ℂ | 1 / 2 < s.re}] (1 / 2)) (𝓝 r) :=
        hE't.mono_left (nhdsWithin_mono _ hsub)
      have hT2 : Tendsto (fun s => G s g) (𝓝[{s : ℂ | 1 / 2 < s.re}] (1 / 2)) (𝓝 r) := by
        refine hT2'.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with s hs
        rw [hE'eq s hs, hGeq s g hs]
      exact tendsto_nhds_unique hT1 hT2
    have hA12 : A (1 / 2) = r * peterssonIntegral K w 𝓕 x y := by
      simp only [hA_def, hG12, peterssonIntegral]
      rw [← integral_const_mul]
      congr 1
      funext g
      ring

    have hχeq : Rτ.centralChar = Rσ.centralChar := by
      ext ⟨z, hz⟩
      have h1 := hZtot z
      simp only [MonoidHom.one_apply, Units.val_one, mul_one] at h1
      have h2 : ((Rσ.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (starRingEnd ℂ) ((Rσ.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) = ((ideleNorm K z ^ (2 * w) : ℝ) : ℂ) := by
        rw [Complex.mul_conj', hωσ z]
        have h0 : 0 ≤ ideleNorm K z := (ideleNorm_pos z).le
        push_cast
        rw [← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul h0]
        norm_num [mul_comm]
      have hσne : (starRingEnd ℂ) ((Rσ.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) ≠ 0 :=
        (map_ne_zero _).mpr (Units.ne_zero _)
      have h3 : ((Rτ.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) = ((Rσ.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) :=
        mul_right_cancel₀ hσne (h1.trans h2.symm)
      have : (⟨z, hz⟩ : ↥((productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))).Z) = ⟨z, Subgroup.mem_top z⟩ := rfl
      rw [this]
      exact h3

    have hres : A (1 / 2) ≠ 0 → ∃ g₁ g₂ : AdelicGL2 (𝓞 K) K,
        peterssonIntegral K w 𝓕 (fun h => Rτ.toFun (h * g₁)) (fun h => Rσ.toFun (h * g₂)) ≠ 0 := by
      intro hA0
      have hPxy : peterssonIntegral K w 𝓕 x y ≠ 0 := by
        intro h0; apply hA0; rw [hA12, h0, mul_zero]
      have hF1' := hF1
      rw [hF1'] at hPxy
      obtain ⟨g₁, hg₁⟩ : ∃ g₁, fx g₁ * peterssonIntegral K w 𝓕 (fun h => Rτ.toFun (h * g₁)) y ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hPxy
        simp only [hall, integral_zero]
      have hg₁' : peterssonIntegral K w 𝓕 (fun h => Rτ.toFun (h * g₁)) y ≠ 0 := fun h0 => hg₁ (by rw [h0, mul_zero])
      have hF2' := hF2 g₁
      rw [hF2'] at hg₁'
      obtain ⟨g₂, hg₂⟩ : ∃ g₂, (starRingEnd ℂ) (fy g₂) *
          peterssonIntegral K w 𝓕 (fun h => Rτ.toFun (h * g₁)) (fun h => Rσ.toFun (h * g₂)) ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hg₁'
        simp only [hall, integral_zero]
      exact ⟨g₁, g₂, fun h0 => hg₂ (by rw [h0, mul_zero])⟩
    refine ⟨S, fx, fy, 1, φ, w, e₁, e₂, a, σ₀, 1 / 2, 1, 𝓕, A, L, ζi, hS, hfx, hfy, hνu, hνF, hZtot, hωσ, hωτ,
      hφ, hφK, hφf, hφjc, hφhol, he₁, he, h𝓕s, h𝓕, ha, hσ₀', one_ne_zero, hAan, hA2,
      fun h => absurd rfl h, fun _ => ⟨rfl, hχeq, hres⟩, hJan.mono hsubT, hJ0,
      hζan0.mono hsub0, fun s hs => ⟨hζne s (hsub0 hs), hζprod s (hsub0 hs)⟩, hLan', hmain⟩
  ·
    have hne : (1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) ≠ ν := fun h => hν1 h.symm
    obtain ⟨aB, s₀, G, haB, hs₀, hGan, hGeq, hGc, hGbd⟩ :=
      AutomorphicForm.exists_analyticOnNhd_sub_mul_bruhatEisenstein_norm_le_archHeight_pow_of_ne_of_isArchKFinite_family K hα
        1 ν hU1 hνu hI1 hνF hne φ hφ hφK hφf hφjc hφhol
    set a : ℝ := max (max aT aB) (1 / 4) with ha_def
    have ha : a < 1 / 2 := by
      rw [ha_def]
      exact max_lt (max_lt haT haB) (by norm_num)
    have haT' : aT ≤ a := le_trans (le_max_left _ _) (le_max_left _ _)
    have haB' : aB ≤ a := le_trans (le_max_right _ _) (le_max_left _ _)
    have ha0 : (0 : ℝ) < a := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hsubT : {s : ℂ | a < s.re} ⊆ {s : ℂ | aT < s.re} := fun s hs => lt_of_le_of_lt haT' hs
    have hsub0 : {s : ℂ | a < s.re} ⊆ {s : ℂ | 0 < s.re} := fun s hs => lt_trans ha0 hs
    obtain ⟨hAan, hA2⟩ := CONT aB s₀ G hGan hGeq hGc hGbd a haB' ha
    set A : ℂ → ℂ := fun s : ℂ => ∫ g in 𝓕, x g * G s g * (starRingEnd ℂ) (y g) *
        ((ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) with hA_def
    refine ⟨S, fx, fy, ν, φ, w, e₁, e₂, a, σ₀, s₀, 1, 𝓕, A, L, ζi, hS, hfx, hfy, hνu, hνF, hZtot, hωσ, hωτ,
      hφ, hφK, hφf, hφjc, hφhol, he₁, he, h𝓕s, h𝓕, ha, hσ₀', one_ne_zero, hAan, hA2,
      fun _ => hs₀, fun h => absurd h hν1, hJan.mono hsubT, hJ0,
      hζan0.mono hsub0, fun s hs => ⟨hζne s (hsub0 hs), hζprod s (hsub0 hs)⟩, hLan', hmain⟩

end

end S_AutomorphicForm_RankinSelberg_exists_testData_analyticOnNhd_sub_mul_peterssonIntegral_and_hasProd_rsEulerPoly_pair
end P2MW
export P2MW.S_AutomorphicForm_RankinSelberg_exists_testData_analyticOnNhd_sub_mul_peterssonIntegral_and_hasProd_rsEulerPoly_pair (solution)
