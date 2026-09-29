-- Prove2me | solution 1 for AutomorphicForm.exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/76d26d31-cb15-5cb9-a182-e522b25fb622

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_AdelicDock_finEmbed_localEmbed_mem_levelOne_inf_finiteAdelicGL2Subgroup
import Theorems.Thm_AutomorphicForm_SiegelCovering_centreCutSiegelSet_coversModCentre_rat
import Theorems.Thm_AutomorphicForm_archHeight_glArch_centralScalar_mul
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat
import Theorems.Thm_AutomorphicForm_exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre
import Theorems.Thm_AutomorphicForm_exists_mem_cuspClasses_levelOne_of_mem_cuspClasses_principalLevel
import Theorems.Thm_AutomorphicForm_heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_AutomorphicForm_isCuspidalFn_rightConv
import Theorems.Thm_AutomorphicForm_isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_isKfSmooth_rightConv
import Theorems.Thm_AutomorphicForm_norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero
import Theorems.Thm_NumberField_AdelicHeight_exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_NumberField_SiegelVolume
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions IsDedekindDomain.HeightOneSpectrum.instSeparableSpaceAdicCompletionOfCountable_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id"
p2m_attr_erase "simp" "TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

section GodementGrowth

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicHeight NumberField.AdelicVolume
p2m_open "AutomorphicForm~continuous_unipotentGL2 P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm AutomorphicForm.WindowedSiegel"

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsArithGenuineCuspRealizable CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsIdeleClassChar finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff lsXiMemberAt_iff IsAutomorphicFnAt unipotentGL2 unipotentGL2_coe unipotentGL2_add unipotentGL2Hom IsCuspidalFn HeckeEigensystem.cNorm SmoothCusp.heckeCosetSum SmoothCusp.IsHeckeCosetEigenfunctionAt HeckeEigensystem SiegelCovering.CoversModCentre SiegelCovering.mul_centralScalar_comm IsSlowlyIncreasingOn IsRapidlyDecreasingOn SiegelCovering.centreCutSiegelSet_coversModCentre_rat archHeight_glArch_centralScalar_mul continuous_and_hasCompactSupport_of_isFactorizableTestFn IsFinTestFactor IsFactorizableTestFn continuous_rightConv_and_contDiff_of_isFactorizableTestFn rightConv rightConv_apply rightConv_comp_mul_left exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat IsIsotypicCuspFormAt isotypicCuspSubmodule_ne_bot_iff cuspClasses exists_isIsotypicCuspFormAt_ne_zero_of_mem_cuspClasses exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre exists_mem_cuspClasses_levelOne_of_mem_cuspClasses_principalLevel heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps ideleNorm_det_globalPoints isCuspidalFn_rightConv isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn isKfSmooth_rightConv norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply integralMatrixSet integralMatrixSet_eq_pi isOpen_integralMatrixSet IsLocalTestFn localIntegralSet mem_localIntegralSet isCompact_localIntegralSet isLocallyConstant_indicator_one unitFinSet one_mem_unitFinSet isCompact_unitFinSet isOpen_unitFinSet unitFinSet_eq_finiteIntegralGL2 indicator_unitFinSet_mul_left isBiInvariantUnder_bot IsUnitFactorizableAt"
namespace GodementEstimate
p2m_open "AutomorphicForm~continuous_unipotentGL2"

private theorem globalPoints_scalar (u : ℚˣ) :
    globalPoints (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) u)
      = centralScalar (𝓞 ℚ) ℚ (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) : ℚ →* AdeleRing (𝓞 ℚ) ℚ) u) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (Matrix.scalar (Fin 2) (u : ℚ) i j)
    = Matrix.scalar (Fin 2) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (u : ℚ)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · rw [if_pos hij, if_pos hij]
  · rw [if_neg hij, if_neg hij, map_zero]

section Character

variable (h : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)

private theorem apply_mul_centralScalar
    (hcentral : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      h (centralScalar (𝓞 ℚ) ℚ z * g) = ((ξ z : ℂˣ) : ℂ) * h g)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    h (g * centralScalar (𝓞 ℚ) ℚ z) = ((ξ z : ℂˣ) : ℂ) * h g := by
  rw [SiegelCovering.mul_centralScalar_comm, hcentral]

private theorem isIdeleClassChar_of_exists_ne_zero
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      h (globalPoints (𝓞 ℚ) ℚ γ * g) = h g)
    (hcentral : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      h (centralScalar (𝓞 ℚ) ℚ z * g) = ((ξ z : ℂˣ) : ℂ) * h g)
    (hne : ∃ g : AdelicGL2 (𝓞 ℚ) ℚ, h g ≠ 0) :
    IsIdeleClassChar (𝓞 ℚ) ℚ ξ := by
  intro u
  obtain ⟨g, hg⟩ := hne
  have h1 : h (globalPoints (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) u) * g) = h g := hleft _ g
  rw [globalPoints_scalar, hcentral] at h1
  have h2 : ((ξ (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) : ℚ →* AdeleRing (𝓞 ℚ) ℚ) u) : ℂˣ) : ℂ) = 1 := by
    apply mul_right_cancel₀ hg
    rw [one_mul]
    exact h1
  exact Units.ext h2

private theorem continuous_centralScalar : Continuous (centralScalar (𝓞 ℚ) ℚ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine ((continuous_pi (fun _ : Fin 2 => Units.continuous_val)).matrix_diagonal).congr ?_
    intro z
    exact (Matrix.scalar_apply (z : AdeleRing (𝓞 ℚ) ℚ)).symm
  · refine ((continuous_pi (fun _ : Fin 2 => Units.continuous_coe_inv)).matrix_diagonal).congr ?_
    intro z
    change Matrix.diagonal (fun _ : Fin 2 => ((z⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ))
      = ((centralScalar (𝓞 ℚ) ℚ z)⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ)
    rw [← map_inv]
    exact (Matrix.scalar_apply ((z⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)).symm

private theorem continuous_xi_of_exists_ne_zero (hcont : Continuous h)
    (hcentral : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      h (centralScalar (𝓞 ℚ) ℚ z * g) = ((ξ z : ℂˣ) : ℂ) * h g)
    (hne : ∃ g : AdelicGL2 (𝓞 ℚ) ℚ, h g ≠ 0) :
    Continuous ξ := by
  obtain ⟨g, hg⟩ := hne
  have hval : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ((ξ z : ℂˣ) : ℂ) = h (centralScalar (𝓞 ℚ) ℚ z * g) / h g := by
    intro z
    rw [hcentral, mul_div_assoc, div_self hg, mul_one]
  have hfun : Continuous fun z : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ((ξ z : ℂˣ) : ℂ) :=
    ((hcont.comp (continuous_centralScalar.mul continuous_const)).div_const (h g)).congr
      (fun z => (hval z).symm)
  refine Units.continuous_iff.mpr ⟨hfun, ?_⟩
  refine (hfun.comp (continuous_inv : Continuous fun z : (AdeleRing (𝓞 ℚ) ℚ)ˣ => z⁻¹)).congr ?_
  intro z
  change ((ξ z⁻¹ : ℂˣ) : ℂ) = (((ξ z)⁻¹ : ℂˣ) : ℂ)
  rw [map_inv]

end Character

section Local

variable {K : Type*} [NormedField K]

private theorem rowMaxNorm_scalar_entries_mul {s : GL (Fin 2) K} {z : K}
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = z)
    (g : GL (Fin 2) K) :
    rowMaxNorm ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = ‖z‖ * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  have hcoe : ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (s : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) := rfl
  have hbot : ∀ j : Fin 2,
      ((s : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)) 1 j
        = z * (g : Matrix (Fin 2) (Fin 2) K) 1 j := by
    intro j
    rw [Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
    ring
  unfold rowMaxNorm
  rw [hcoe, hbot 0, hbot 1, norm_mul, norm_mul]
  exact (mul_max_of_nonneg _ _ (norm_nonneg z)).symm

private theorem finLocalHeight_scalar_entries_mul {s : GL (Fin 2) K} {z : K} (hz : z ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) K) 0 0 = z)
    (h01 : (s : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = z)
    (g : GL (Fin 2) K) :
    finLocalHeight (s * g) = finLocalHeight g := by
  have hcoe : ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (s : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) := rfl
  have hdets : (s : Matrix (Fin 2) (Fin 2) K).det = z ^ 2 := by
    rw [Matrix.det_fin_two, h00, h01, h10, h11]
    ring
  have hdet : ‖((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖
      = ‖z‖ ^ 2 * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ := by
    rw [hcoe, Matrix.det_mul, hdets, norm_mul, norm_pow]
  have hz2 : (0 : ℝ) < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.2 hz) 2
  have hrow := rowMaxNorm_scalar_entries_mul h10 h11 g
  have hpos := rowMaxNorm_pos g
  unfold finLocalHeight
  rw [hdet, hrow, mul_pow,
    div_eq_div_iff (mul_pos hz2 (pow_pos hpos 2)).ne' (pow_pos hpos 2).ne']
  ring

end Local

section Adelic

variable (F : Type) [Field F] [NumberField F]

private theorem finHeight_glFin_centralScalar_mul (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    finHeight F (glFin (𝓞 F) F (centralScalar (𝓞 F) F z * g)) = finHeight F (glFin (𝓞 F) F g) := by
  unfold finHeight
  refine finprod_congr fun v => ?_
  rw [map_mul, map_mul]

  set zv : v.adicCompletion F := ((z : AdeleRing (𝓞 F) F).2 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) v with hzv
  have hmul :
      zv * ((((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) v)
        = 1 := by
    have h1 : (z : AdeleRing (𝓞 F) F) * ((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) = 1 := z.mul_inv
    exact congrArg (fun a : AdeleRing (𝓞 F) F => (a.2 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) v) h1
  have hunit : zv ≠ 0 := left_ne_zero_of_mul_eq_one hmul
  have hentry : ∀ i j : Fin 2,
      (finComponent (𝓞 F) F v (glFin (𝓞 F) F (centralScalar (𝓞 F) F z)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j
        = (((centralScalar (𝓞 F) F z : AdelicGL2 (𝓞 F) F) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v := fun _ _ => rfl
  refine finLocalHeight_scalar_entries_mul hunit ?_ ?_ ?_ ?_ _
  · rw [hentry, centralScalar_apply_eq, hzv]
  · rw [hentry, centralScalar_apply_ne _ (by decide)]
    rfl
  · rw [hentry, centralScalar_apply_ne _ (by decide)]
    rfl
  · rw [hentry, centralScalar_apply_eq, hzv]

private theorem adelicHeight_centralScalar_mul (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (centralScalar (𝓞 F) F z * g) = adelicHeight F g := by
  unfold adelicHeight
  rw [AutomorphicForm.archHeight_glArch_centralScalar_mul F z g, finHeight_glFin_centralScalar_mul F z g]

end Adelic

section Rat

private theorem default_infinitePlace_rat_mult : (default : InfinitePlace ℚ).mult = 1 := by
  have hd : (default : InfinitePlace ℚ) = Rat.infinitePlace := Subsingleton.elim _ _
  rw [hd]
  unfold InfinitePlace.mult
  rw [if_pos Rat.isReal_infinitePlace]

private theorem le_adelicHeight_of_mem_centreCutSiegelSet {c u d₁ d₂ : ℝ} {x : AdelicGL2 (𝓞 ℚ) ℚ}
    (hx : x ∈ centreCutSiegelSet ℚ c u d₁ d₂) : c ≤ adelicHeight ℚ x := by
  rw [adelicHeight_eq_archHeight_of_mem hx.1]
  unfold archHeight
  rw [Fintype.prod_unique, default_infinitePlace_rat_mult, pow_one]
  exact hx.2.1 default

private theorem ideleNorm_det_mem_Icc_of_mem_centreCutSiegelSet {c u d₁ d₂ : ℝ} {x : AdelicGL2 (𝓞 ℚ) ℚ}
    (hx : x ∈ centreCutSiegelSet ℚ c u d₁ d₂) :
    NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc d₁ d₂ := by
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult ℚ x hx.1, Fintype.prod_unique,
    default_infinitePlace_rat_mult, pow_one]
  exact hx.2.2.2 default

end Rat

section Growth

open NumberField.TateGlobal

private def coveringSet : Set (AdelicGL2 (𝓞 ℚ) ℚ) := centreCutSiegelSet ℚ (Real.sqrt 3 / 2) (1 / 2) 1 1

private theorem coversModCentre_coveringSet : SiegelCovering.CoversModCentre ℚ coveringSet :=
  SiegelCovering.centreCutSiegelSet_coversModCentre_rat le_rfl le_rfl one_pos le_rfl

private theorem det_centralScalar_eq_sq (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 ℚ) ℚ z) = z ^ 2 := by
  rw [show centralScalar (𝓞 ℚ) ℚ = Matrix.GeneralLinearGroup.scalar (Fin 2) from rfl,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

private theorem ideleNorm_det_eq_one_of_mem_coveringSet {w : AdelicGL2 (𝓞 ℚ) ℚ} (hw : w ∈ coveringSet) :
    ideleNorm ℚ (Matrix.GeneralLinearGroup.det w) = 1 :=
  le_antisymm (ideleNorm_det_mem_Icc_of_mem_centreCutSiegelSet hw).2
    (ideleNorm_det_mem_Icc_of_mem_centreCutSiegelSet hw).1

private theorem exists_ideleNorm_det_bounds (C : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (hC : IsCompact C) :
    ∃ m M : ℝ, 0 < m ∧ ∀ s ∈ C,
      m ≤ ideleNorm ℚ (Matrix.GeneralLinearGroup.det s) ∧ ideleNorm ℚ (Matrix.GeneralLinearGroup.det s) ≤ M := by
  rcases C.eq_empty_or_nonempty with hempty | hne
  · refine ⟨1, 1, one_pos, fun s hs => ?_⟩
    rw [hempty] at hs
    exact hs.elim
  have hcont : ContinuousOn (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ideleNorm ℚ (Matrix.GeneralLinearGroup.det g)) C :=
    (continuous_ideleNorm_det ℚ).continuousOn
  obtain ⟨s₀, _, hmin⟩ := hC.exists_isMinOn hne hcont
  obtain ⟨s₁, _, hmax⟩ := hC.exists_isMaxOn hne hcont
  exact ⟨ideleNorm ℚ (Matrix.GeneralLinearGroup.det s₀), ideleNorm ℚ (Matrix.GeneralLinearGroup.det s₁),
    ideleNorm_pos _, fun s hs => ⟨isMinOn_iff.mp hmin s hs, isMaxOn_iff.mp hmax s hs⟩⟩

private theorem exists_height_globalPoints_mul_le (C : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (hC : IsCompact C)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ centreCutSiegelSet ℚ c u d₁ d₂, ∀ s ∈ C, ∀ γ : Matrix.GeneralLinearGroup (Fin 2) ℚ,
      adelicHeight ℚ (globalPoints (𝓞 ℚ) ℚ γ * (x * s)) ≤ L * max 1 (adelicHeight ℚ x) := by
  obtain ⟨κ, K, hκ, hcomp⟩ := exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact ℚ C hC
  have hκc : 0 < κ * c := mul_pos hκ hc
  have hL0 : (0 : ℝ) ≤ max K (κ * c)⁻¹ := le_max_of_le_right (inv_pos.mpr hκc).le
  refine ⟨max K (κ * c)⁻¹, hL0, ?_⟩
  intro x hx s hs γ
  have hxpos : 0 < adelicHeight ℚ x := adelicHeight_pos x
  have hmax1 : (1 : ℝ) ≤ max 1 (adelicHeight ℚ x) := le_max_left _ _
  have hxmax : adelicHeight ℚ x ≤ max 1 (adelicHeight ℚ x) := le_max_right _ _
  obtain ⟨hlow, hup⟩ := hcomp x s hs
  by_cases hγ : (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0
  · rw [adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero ℚ γ hγ]
    calc adelicHeight ℚ (x * s) ≤ K * adelicHeight ℚ x := hup
      _ ≤ max K (κ * c)⁻¹ * adelicHeight ℚ x := mul_le_mul_of_nonneg_right (le_max_left _ _) hxpos.le
      _ ≤ max K (κ * c)⁻¹ * max 1 (adelicHeight ℚ x) := mul_le_mul_of_nonneg_left hxmax hL0
  · have hprod := adelicHeight_globalPoints_mul_mul_adelicHeight_le_one γ hγ (x * s)
    have hy : κ * c ≤ adelicHeight ℚ (x * s) :=
      (mul_le_mul_of_nonneg_left (le_adelicHeight_of_mem_centreCutSiegelSet hx) hκ.le).trans hlow
    have hypos : 0 < adelicHeight ℚ (x * s) := hκc.trans_le hy
    calc adelicHeight ℚ (globalPoints (𝓞 ℚ) ℚ γ * (x * s)) ≤ 1 / adelicHeight ℚ (x * s) :=
          (le_div_iff₀ hypos).mpr hprod
      _ ≤ 1 / (κ * c) := one_div_le_one_div_of_le hκc hy
      _ = (κ * c)⁻¹ := one_div _
      _ ≤ max K (κ * c)⁻¹ := le_max_right _ _
      _ = max K (κ * c)⁻¹ * 1 := (mul_one _).symm
      _ ≤ max K (κ * c)⁻¹ * max 1 (adelicHeight ℚ x) := mul_le_mul_of_nonneg_left hmax1 hL0

private theorem exists_norm_xi_ge (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hξ : IsIdeleClassChar (𝓞 ℚ) ℚ ξ)
    (hξc : Continuous ξ) (C : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (hC : IsCompact C) (c u d₁ d₂ : ℝ) (hd₁ : 0 < d₁) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ centreCutSiegelSet ℚ c u d₁ d₂, ∀ s ∈ C,
      ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ),
        globalPoints (𝓞 ℚ) ℚ γ * (x * s) * centralScalar (𝓞 ℚ) ℚ z ∈ coveringSet →
          ε ≤ ‖((ξ z : ℂˣ) : ℂ)‖ := by
  obtain ⟨σ, hσ⟩ := exists_norm_apply_eq_ideleNorm_rpow ℚ ξ hξ hξc
  obtain ⟨m, M, hm, hbounds⟩ := exists_ideleNorm_det_bounds C hC
  have ha : 0 < d₁ * m := mul_pos hd₁ hm
  have hb : 0 < max (d₂ * M) (d₁ * m) := ha.trans_le (le_max_right _ _)
  refine ⟨Real.sqrt (min ((max (d₂ * M) (d₁ * m))⁻¹ ^ σ) ((d₁ * m)⁻¹ ^ σ)), ?_, ?_⟩
  · exact Real.sqrt_pos.mpr
      (lt_min (Real.rpow_pos_of_pos (inv_pos.mpr hb) σ) (Real.rpow_pos_of_pos (inv_pos.mpr ha) σ))
  intro x hx s hs γ z hw
  set q : ℝ := ideleNorm ℚ (Matrix.GeneralLinearGroup.det x) * ideleNorm ℚ (Matrix.GeneralLinearGroup.det s)
    with hq_def
  have hxIcc := ideleNorm_det_mem_Icc_of_mem_centreCutSiegelSet hx
  obtain ⟨hs₁, hs₂⟩ := hbounds s hs
  have hspos : 0 < ideleNorm ℚ (Matrix.GeneralLinearGroup.det s) := ideleNorm_pos _
  have hxpos : 0 < ideleNorm ℚ (Matrix.GeneralLinearGroup.det x) := ideleNorm_pos _
  have hqa : d₁ * m ≤ q := mul_le_mul hxIcc.1 hs₁ hm.le hxpos.le
  have hqb : q ≤ max (d₂ * M) (d₁ * m) :=
    (mul_le_mul hxIcc.2 hs₂ hspos.le (hxpos.le.trans hxIcc.2)).trans (le_max_left _ _)
  have hqpos : 0 < q := ha.trans_le hqa

  have hdet : ideleNorm ℚ (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 ℚ) ℚ γ))
      * q * (ideleNorm ℚ z * ideleNorm ℚ z) = 1 := by
    have h1 := ideleNorm_det_eq_one_of_mem_coveringSet hw
    rw [hq_def]
    simpa only [map_mul, det_centralScalar_eq_sq, pow_two, ideleNorm_mul] using h1
  rw [ideleNorm_det_globalPoints γ, one_mul] at hdet
  have hzz : ideleNorm ℚ z * ideleNorm ℚ z = q⁻¹ := eq_inv_of_mul_eq_one_right hdet

  have hsq : ‖((ξ z : ℂˣ) : ℂ)‖ ^ 2 = q⁻¹ ^ σ := by
    rw [pow_two, ← norm_mul, ← Units.val_mul, ← map_mul, hσ, ideleNorm_mul, hzz]
  have hinv₁ : (max (d₂ * M) (d₁ * m))⁻¹ ≤ q⁻¹ := inv_anti₀ hqpos hqb
  have hinv₂ : q⁻¹ ≤ (d₁ * m)⁻¹ := inv_anti₀ ha hqa
  have hε₂ : min ((max (d₂ * M) (d₁ * m))⁻¹ ^ σ) ((d₁ * m)⁻¹ ^ σ) ≤ q⁻¹ ^ σ := by
    rcases le_or_gt 0 σ with hσ0 | hσ0
    · exact (min_le_left _ _).trans (Real.rpow_le_rpow (inv_pos.mpr hb).le hinv₁ hσ0)
    · exact (min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos (inv_pos.mpr hqpos) hinv₂ hσ0.le)
  calc Real.sqrt (min ((max (d₂ * M) (d₁ * m))⁻¹ ^ σ) ((d₁ * m)⁻¹ ^ σ))
      ≤ Real.sqrt (‖((ξ z : ℂˣ) : ℂ)‖ ^ 2) := Real.sqrt_le_sqrt (hsq ▸ hε₂)
    _ = ‖((ξ z : ℂˣ) : ℂ)‖ := Real.sqrt_sq (norm_nonneg _)

private theorem exists_norm_apply_mul_le (h : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hcont : Continuous h)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      h (globalPoints (𝓞 ℚ) ℚ γ * g) = h g)
    (hcentral : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      h (centralScalar (𝓞 ℚ) ℚ z * g) = ((ξ z : ℂˣ) : ℂ) * h g)
    (hgrowth : ∀ c u d₁ d₂ : ℝ, 0 < c → 0 < d₁ →
      IsSlowlyIncreasingOn (centreCutSiegelSet ℚ c u d₁ d₂) (adelicHeight ℚ) h)
    (C : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (hC : IsCompact C) (c u d₁ d₂ : ℝ) (hc : 0 < c) (hd₁ : 0 < d₁) :
    ∃ (B : ℝ) (N : ℕ), ∀ x ∈ centreCutSiegelSet ℚ c u d₁ d₂, ∀ s ∈ C,
      ‖h (x * s)‖ ≤ B * max 1 (adelicHeight ℚ x) ^ N := by
  by_cases hzero : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, h g = 0
  · refine ⟨0, 0, fun x _ s _ => ?_⟩
    rw [hzero, norm_zero, zero_mul]
  have hne : ∃ g : AdelicGL2 (𝓞 ℚ) ℚ, h g ≠ 0 := by
    push Not at hzero
    exact hzero
  have hξ : IsIdeleClassChar (𝓞 ℚ) ℚ ξ := isIdeleClassChar_of_exists_ne_zero h ξ hleft hcentral hne
  have hξc : Continuous ξ := continuous_xi_of_exists_ne_zero h ξ hcont hcentral hne
  obtain ⟨A, N, hA⟩ := hgrowth (Real.sqrt 3 / 2) (1 / 2) 1 1 (by positivity) one_pos
  obtain ⟨L, hL0, hL⟩ := exists_height_globalPoints_mul_le C hC c u d₁ d₂ hc
  obtain ⟨ε, hε, hεle⟩ := exists_norm_xi_ge ξ hξ hξc C hC c u d₁ d₂ hd₁
  refine ⟨max A 0 * L ^ N * ε⁻¹, N, ?_⟩
  intro x hx s hs
  obtain ⟨γ, z, hw⟩ := coversModCentre_coveringSet (x * s)
  set w := globalPoints (𝓞 ℚ) ℚ γ * (x * s) * centralScalar (𝓞 ℚ) ℚ z with hw_def

  have hvalue : h w = ((ξ z : ℂˣ) : ℂ) * h (x * s) := by
    rw [hw_def, apply_mul_centralScalar h ξ hcentral, hleft]
  have hnorm : ‖h (x * s)‖ * ‖((ξ z : ℂˣ) : ℂ)‖ = ‖h w‖ := by
    rw [hvalue, norm_mul, mul_comm]

  have hheight : adelicHeight ℚ w ≤ L * max 1 (adelicHeight ℚ x) := by
    rw [hw_def, SiegelCovering.mul_centralScalar_comm, adelicHeight_centralScalar_mul]
    exact hL x hx s hs γ
  have hwpos : 0 ≤ adelicHeight ℚ w := (adelicHeight_pos w).le
  have hgrow : ‖h w‖ ≤ max A 0 * (L * max 1 (adelicHeight ℚ x)) ^ N :=
    calc ‖h w‖ ≤ A * adelicHeight ℚ w ^ N := hA w hw
      _ ≤ max A 0 * adelicHeight ℚ w ^ N := mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hwpos N)
      _ ≤ max A 0 * (L * max 1 (adelicHeight ℚ x)) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hwpos hheight N) (le_max_right _ _)
  have hstep : ‖h (x * s)‖ * ε ≤ max A 0 * L ^ N * max 1 (adelicHeight ℚ x) ^ N := by
    calc ‖h (x * s)‖ * ε ≤ ‖h (x * s)‖ * ‖((ξ z : ℂˣ) : ℂ)‖ :=
          mul_le_mul_of_nonneg_left (hεle x hx s hs γ z hw) (norm_nonneg _)
      _ = ‖h w‖ := hnorm
      _ ≤ max A 0 * (L * max 1 (adelicHeight ℚ x)) ^ N := hgrow
      _ = max A 0 * L ^ N * max 1 (adelicHeight ℚ x) ^ N := by rw [mul_pow, mul_assoc]
  calc ‖h (x * s)‖ = ‖h (x * s)‖ * ε * ε⁻¹ := (mul_inv_cancel_right₀ hε.ne' _).symm
    _ ≤ max A 0 * L ^ N * max 1 (adelicHeight ℚ x) ^ N * ε⁻¹ :=
        mul_le_mul_of_nonneg_right hstep (inv_pos.mpr hε).le
    _ = max A 0 * L ^ N * ε⁻¹ * max 1 (adelicHeight ℚ x) ^ N := by ring

end Growth

end AutomorphicForm.GodementEstimate

end

end GodementGrowth

section UnipotentAverage

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField NumberField.AdelicHaar NumberField.AdelicBox AutomorphicForm~continuous_unipotentGL2 P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm MeasureTheory"

noncomputable section

namespace UnipotentAverage

private def unipotentAverage (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (x y : AdelicGL2 (𝓞 ℚ) ℚ) : ℂ :=
  (((adelicAddHaar (𝓞 ℚ) ℚ) (adelicBox ℚ)).toReal : ℂ)⁻¹ *
    ∫ t, f (x⁻¹ * unipotentGL2 t * y) ∂(adelicAddHaar (𝓞 ℚ) ℚ)

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

private theorem exists_ne_zero_of_unipotentAverage_ne_zero {f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} {x y : AdelicGL2 (𝓞 ℚ) ℚ}
    (h : unipotentAverage f x y ≠ 0) : ∃ t : AdeleRing (𝓞 ℚ) ℚ, f (x⁻¹ * unipotentGL2 t * y) ≠ 0 := by
  by_contra hcon
  simp only [not_exists, ne_eq, not_not] at hcon
  apply h
  simp only [unipotentAverage, hcon, integral_zero, mul_zero]

private theorem unipotentAverage_unipotentGL2_mul (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (x : AdelicGL2 (𝓞 ℚ) ℚ)
    (s : AdeleRing (𝓞 ℚ) ℚ) (y : AdelicGL2 (𝓞 ℚ) ℚ) :
    unipotentAverage f x (unipotentGL2 s * y) = unipotentAverage f x y := by
  unfold unipotentAverage
  congr 1
  have h : ∀ t : AdeleRing (𝓞 ℚ) ℚ,
      x⁻¹ * unipotentGL2 t * (unipotentGL2 s * y) = x⁻¹ * unipotentGL2 (s + t) * y := by
    intro t
    rw [add_comm, unipotentGL2_add]
    simp only [mul_assoc]
  simp_rw [h]
  exact integral_add_left_eq_self (fun t => f (x⁻¹ * unipotentGL2 t * y)) s

private theorem countable_ideal_of_countable {R : Type*} [CommRing R] [IsNoetherianRing R] [Countable R] :
    Countable (Ideal R) := by
  have hfg : ∀ I : Ideal R, ∃ S : Finset R, Ideal.span (↑S : Set R) = I := fun I => Ideal.fg_of_isNoetherianRing I
  choose gens hgens using hfg
  refine (show Function.Injective gens from ?_).countable
  intro I J h
  calc I = Ideal.span (↑(gens I) : Set R) := (hgens I).symm
    _ = Ideal.span (↑(gens J) : Set R) := by rw [h]
    _ = J := hgens J

private theorem countable_heightOneSpectrum_of_countable {R : Type*} [CommRing R] [IsDedekindDomain R] [Countable R] :
    Countable (HeightOneSpectrum R) :=
  haveI : Countable (Ideal R) := countable_ideal_of_countable
  (show Function.Injective (HeightOneSpectrum.asIdeal : HeightOneSpectrum R → Ideal R) from
    fun _ _ h => HeightOneSpectrum.ext h).countable

private scoped instance countable_ringOfIntegers_rat : Countable (𝓞 ℚ) := (RingOfIntegers.coe_injective (K := ℚ)).countable

private scoped instance countable_heightOneSpectrum_rat : Countable (HeightOneSpectrum (𝓞 ℚ)) :=
  countable_heightOneSpectrum_of_countable

private scoped instance secondCountableTopology_finiteAdeleRing_rat : SecondCountableTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  RestrictedProduct.secondCountableTopology fun v : HeightOneSpectrum (𝓞 ℚ) =>
    Valued.isOpen_valuationSubring (v.adicCompletion ℚ)

private scoped instance secondCountableTopology_infinitePlace_completion_rat (v : InfinitePlace ℚ) :
    SecondCountableTopology v.Completion :=
  haveI : Countable (WithAbs v.1) := Countable.of_equiv ℚ (WithAbs.equiv v.1).symm.toEquiv
  haveI : SecondCountableTopology v.1.Completion := UniformSpace.secondCountable_of_separable _
  (NumberField.InfinitePlace.Completion.isometry_toCompletion (v := v)).isEmbedding.secondCountableTopology

private scoped instance secondCountableTopology_infiniteAdeleRing_rat : SecondCountableTopology (InfiniteAdeleRing ℚ) :=
  inferInstanceAs (SecondCountableTopology ((v : InfinitePlace ℚ) → v.Completion))

private scoped instance secondCountableTopology_adeleRing_rat : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) :=
  inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ))

private theorem continuous_unipotentGL2 :
    Continuous fun t : AdeleRing (𝓞 ℚ) ℚ => (unipotentGL2 t : AdelicGL2 (𝓞 ℚ) ℚ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [unipotentGL2] <;> first | exact continuous_const | exact continuous_id
  · have h : ∀ t : AdeleRing (𝓞 ℚ) ℚ,
        (((unipotentGL2 t)⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) =
          !![1, -t; 0, 1] :=
      fun t => rfl
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp <;> first | exact continuous_const | exact continuous_id | exact continuous_neg

private theorem continuous_integrand {f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hfc : Continuous f) (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    Continuous fun p : AdelicGL2 (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => f (x⁻¹ * unipotentGL2 p.2 * p.1) :=
  hfc.comp ((continuous_const.mul (continuous_unipotentGL2.comp continuous_snd)).mul continuous_fst)

private theorem aestronglyMeasurable_unipotentAverage {f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hfc : Continuous f)
    (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    AEStronglyMeasurable (unipotentAverage f x) (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := by
  have hF : StronglyMeasurable
      fun p : AdelicGL2 (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => f (x⁻¹ * unipotentGL2 p.2 * p.1) :=
    (continuous_integrand hfc x).stronglyMeasurable
  have hI : StronglyMeasurable
      fun y : AdelicGL2 (𝓞 ℚ) ℚ => ∫ t, f (x⁻¹ * unipotentGL2 t * y) ∂(adelicAddHaar (𝓞 ℚ) ℚ) :=
    hF.integral_prod_right'
  exact (hI.const_mul ((((adelicAddHaar (𝓞 ℚ) ℚ) (adelicBox ℚ)).toReal : ℂ)⁻¹)).aestronglyMeasurable

private theorem exists_norm_unipotentAverage_le {f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hfc : Continuous f)
    (hfs : HasCompactSupport f) (x : AdelicGL2 (𝓞 ℚ) ℚ) (Q : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (hQ : IsCompact Q) :
    ∃ B : ℝ, ∀ y ∈ Q, ‖unipotentAverage f x y‖ ≤ B := by
  obtain ⟨C, hC⟩ := hfc.bounded_above_of_compact_support hfs

  obtain ⟨T, hTc, hT⟩ : ∃ T : Set (AdeleRing (𝓞 ℚ) ℚ), IsCompact T ∧
      ∀ y ∈ Q, ∀ t : AdeleRing (𝓞 ℚ) ℚ, t ∉ T → f (x⁻¹ * unipotentGL2 t * y) = 0 := by
    have hφ : Continuous fun p : AdelicGL2 (𝓞 ℚ) ℚ × AdelicGL2 (𝓞 ℚ) ℚ =>
        ((x * p.1 * p.2⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 0 1 :=
      (Units.continuous_val.comp ((continuous_const.mul continuous_fst).mul continuous_snd.inv)).matrix_elem 0 1
    refine ⟨_, (hfs.isCompact.prod hQ).image hφ, ?_⟩
    intro y hy t ht
    by_contra hne
    apply ht
    refine ⟨(x⁻¹ * unipotentGL2 t * y, y), ⟨subset_tsupport f (Function.mem_support.2 hne), hy⟩, ?_⟩
    have hmat : x * (x⁻¹ * unipotentGL2 t * y) * y⁻¹ = unipotentGL2 t := by group
    simp [hmat]
  refine ⟨‖(((adelicAddHaar (𝓞 ℚ) ℚ) (adelicBox ℚ)).toReal : ℂ)⁻¹‖ * (C * (adelicAddHaar (𝓞 ℚ) ℚ).real T),
    fun y hy => ?_⟩
  unfold unipotentAverage
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖∫ t, f (x⁻¹ * unipotentGL2 t * y) ∂(adelicAddHaar (𝓞 ℚ) ℚ)‖
      = ‖∫ t in T, f (x⁻¹ * unipotentGL2 t * y) ∂(adelicAddHaar (𝓞 ℚ) ℚ)‖ := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => hT y hy t ht]
    _ ≤ C * (adelicAddHaar (𝓞 ℚ) ℚ).real T :=
        norm_setIntegral_le_of_norm_le_const hTc.measure_lt_top fun t _ => hC _

end UnipotentAverage
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage"

end UnipotentAverage
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage"

section UnipotentDomain

set_option autoImplicit false

open IsDedekindDomain MeasureTheory NumberField NumberField.AdelicHaar NumberField.TateGlobal
p2m_open "AutomorphicForm~continuous_unipotentGL2 P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open scoped Pointwise

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsArithGenuineCuspRealizable CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsIdeleClassChar finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff lsXiMemberAt_iff IsAutomorphicFnAt unipotentGL2 unipotentGL2_coe unipotentGL2_add unipotentGL2Hom IsCuspidalFn HeckeEigensystem.cNorm SmoothCusp.heckeCosetSum SmoothCusp.IsHeckeCosetEigenfunctionAt HeckeEigensystem SiegelCovering.CoversModCentre SiegelCovering.mul_centralScalar_comm IsSlowlyIncreasingOn IsRapidlyDecreasingOn SiegelCovering.centreCutSiegelSet_coversModCentre_rat archHeight_glArch_centralScalar_mul continuous_and_hasCompactSupport_of_isFactorizableTestFn IsFinTestFactor IsFactorizableTestFn continuous_rightConv_and_contDiff_of_isFactorizableTestFn rightConv rightConv_apply rightConv_comp_mul_left exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat IsIsotypicCuspFormAt isotypicCuspSubmodule_ne_bot_iff cuspClasses exists_isIsotypicCuspFormAt_ne_zero_of_mem_cuspClasses exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre exists_mem_cuspClasses_levelOne_of_mem_cuspClasses_principalLevel heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps ideleNorm_det_globalPoints isCuspidalFn_rightConv isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn isKfSmooth_rightConv norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply integralMatrixSet integralMatrixSet_eq_pi isOpen_integralMatrixSet IsLocalTestFn localIntegralSet mem_localIntegralSet isCompact_localIntegralSet isLocallyConstant_indicator_one unitFinSet one_mem_unitFinSet isCompact_unitFinSet isOpen_unitFinSet unitFinSet_eq_finiteIntegralGL2 indicator_unitFinSet_mul_left isBiInvariantUnder_bot IsUnitFactorizableAt"
namespace GodementEstimate
p2m_open "AutomorphicForm~continuous_unipotentGL2"

section Subgroup

variable {Γ H X : Type*} [Group Γ] [Group H] [Countable Γ] [MulAction Γ X] [MulAction H X] [MeasurableSpace X]
  [MeasurableConstSMul Γ X] {μ : Measure X} [SMulInvariantMeasure Γ X μ]

private theorem isFundamentalDomain_iUnion_out_smul {s : Set X} (hs : IsFundamentalDomain Γ s μ) (φ : H →* Γ)
    (hφ : Function.Injective φ) (hcompat : ∀ (k : H) (x : X), k • x = φ k • x) :
    IsFundamentalDomain H (⋃ q : Quotient (QuotientGroup.rightRel φ.range), (Quotient.out q) • s) μ := by
  have hset : ∀ (k : H) (t : Set X), k • t = φ k • t := by
    intro k t
    ext x
    simp only [Set.mem_smul_set, hcompat]
  refine IsFundamentalDomain.mk'' (NullMeasurableSet.iUnion fun q => hs.nullMeasurableSet_smul (Quotient.out q))
    ?_ ?_ ?_
  · refine hs.ae_covers.mono fun x hx => ?_
    obtain ⟨γ, hγ⟩ := hx
    set q : Quotient (QuotientGroup.rightRel φ.range) := Quotient.mk _ γ⁻¹ with hq
    have hrel : γ⁻¹ * (Quotient.out q)⁻¹ ∈ φ.range :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact (Quotient.out_eq q))
    obtain ⟨k, hk⟩ := hrel
    refine ⟨k⁻¹, Set.mem_iUnion.mpr ⟨q, ?_⟩⟩
    rw [hcompat, map_inv, hk, mul_inv_rev, inv_inv, inv_inv, mul_smul]
    exact Set.smul_mem_smul_set hγ
  · intro β hβ
    rw [hset, Set.smul_set_iUnion]
    refine AEDisjoint.iUnion_left_iff.mpr fun q => AEDisjoint.iUnion_right_iff.mpr fun q' => ?_
    rw [smul_smul]
    refine hs.aedisjoint fun h => hβ ?_
    have hqq : q = q' := by
      rw [← Quotient.out_eq q, ← Quotient.out_eq q']
      exact Quotient.sound (QuotientGroup.rightRel_apply.mpr ⟨β, by rw [← h, mul_inv_cancel_right]⟩)
    subst hqq
    have h1 : φ β = 1 :=
      calc φ β = φ β * Quotient.out q * (Quotient.out q)⁻¹ := (mul_inv_cancel_right _ _).symm
        _ = Quotient.out q * (Quotient.out q)⁻¹ := by rw [h]
        _ = 1 := mul_inv_cancel _
    exact hφ (h1.trans (map_one φ).symm)
  · intro β
    have hfun : (fun x : X => β • x) = fun x => φ β • x := funext (hcompat β)
    rw [hfun]
    exact (measurePreserving_smul (φ β) μ).quasiMeasurePreserving

end Subgroup
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage"

section Rat

private abbrev detSlab (e₁ e₂ : ℝ) : Set (AdelicGL2 (𝓞 ℚ) ℚ) :=
  {g | ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}

private theorem ideleNorm_one' : ideleNorm ℚ (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ) = 1 := by
  have h := ideleNorm_mul (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ) 1
  rw [one_mul] at h
  exact mul_right_cancel₀ (ideleNorm_pos (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ)).ne' (h.symm.trans (one_mul _).symm)

private
theorem ideleNorm_det_inv_eq_one {g : AdelicGL2 (𝓞 ℚ) ℚ} (hg : ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) = 1) :
    ideleNorm ℚ (Matrix.GeneralLinearGroup.det g⁻¹) = 1 := by
  have h := ideleNorm_mul (Matrix.GeneralLinearGroup.det g⁻¹) (Matrix.GeneralLinearGroup.det g)
  rw [← map_mul, inv_mul_cancel, map_one, ideleNorm_one', hg, mul_one] at h
  exact h.symm

private theorem ideleNorm_det_unipotentGL2 (t : AdeleRing (𝓞 ℚ) ℚ) :
    ideleNorm ℚ (Matrix.GeneralLinearGroup.det (unipotentGL2 t)) = 1 := by
  have h : Matrix.GeneralLinearGroup.det (unipotentGL2 t) = 1 := by
    apply Units.ext
    show Matrix.det !![(1 : AdeleRing (𝓞 ℚ) ℚ), t; 0, 1] = 1
    simp [Matrix.det_fin_two_of]
  rw [h, ideleNorm_one']

private theorem mul_mem_detSlab_iff (e₁ e₂ : ℝ) {g : AdelicGL2 (𝓞 ℚ) ℚ}
    (hg : ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) = 1) (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    g * x ∈ detSlab e₁ e₂ ↔ x ∈ detSlab e₁ e₂ := by
  simp only [detSlab, Set.mem_setOf_eq, map_mul, ideleNorm_mul, hg, one_mul]

private theorem countable_ideal_of_countable {R : Type*} [CommRing R] [IsNoetherianRing R] [Countable R] :
    Countable (Ideal R) := by
  have hfg : ∀ I : Ideal R, ∃ S : Finset R, Ideal.span (↑S : Set R) = I := fun I => Ideal.fg_of_isNoetherianRing I
  choose gens hgens using hfg
  refine (show Function.Injective gens from ?_).countable
  intro I J h
  calc I = Ideal.span (↑(gens I) : Set R) := (hgens I).symm
    _ = Ideal.span (↑(gens J) : Set R) := by rw [h]
    _ = J := hgens J

private theorem countable_heightOneSpectrum_of_countable {R : Type*} [CommRing R] [IsDedekindDomain R] [Countable R] :
    Countable (HeightOneSpectrum R) :=
  haveI : Countable (Ideal R) := countable_ideal_of_countable
  (show Function.Injective (HeightOneSpectrum.asIdeal : HeightOneSpectrum R → Ideal R) from
    fun _ _ h => HeightOneSpectrum.ext h).countable

private scoped instance countable_ringOfIntegers_rat : Countable (𝓞 ℚ) := (RingOfIntegers.coe_injective (K := ℚ)).countable

private scoped instance countable_heightOneSpectrum_rat : Countable (HeightOneSpectrum (𝓞 ℚ)) :=
  countable_heightOneSpectrum_of_countable

private scoped instance secondCountableTopology_finiteAdeleRing_rat : SecondCountableTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  RestrictedProduct.secondCountableTopology fun v : HeightOneSpectrum (𝓞 ℚ) =>
    Valued.isOpen_valuationSubring (v.adicCompletion ℚ)

private scoped instance secondCountableTopology_infinitePlace_completion_rat (v : InfinitePlace ℚ) :
    SecondCountableTopology v.Completion :=
  haveI : Countable (WithAbs v.1) := Countable.of_equiv ℚ (WithAbs.equiv v.1).symm.toEquiv
  haveI : SecondCountableTopology v.1.Completion := UniformSpace.secondCountable_of_separable _
  (NumberField.InfinitePlace.Completion.isometry_toCompletion (v := v)).isEmbedding.secondCountableTopology

private scoped instance secondCountableTopology_infiniteAdeleRing_rat : SecondCountableTopology (InfiniteAdeleRing ℚ) :=
  inferInstanceAs (SecondCountableTopology ((v : InfinitePlace ℚ) → v.Completion))

private scoped instance secondCountableTopology_adeleRing_rat : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) :=
  inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ))

private scoped instance secondCountableTopology_matrix_adeleRing_rat :
    SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → AdeleRing (𝓞 ℚ) ℚ))

private scoped instance secondCountableTopology_mulOpposite {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] :
    SecondCountableTopology Mᵐᵒᵖ :=
  (MulOpposite.opHomeomorph : M ≃ₜ Mᵐᵒᵖ).symm.isInducing.secondCountableTopology

private scoped instance secondCountableTopology_adelicGL2_rat : SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ) :=
  (Units.isEmbedding_embedProduct (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))).secondCountableTopology

private scoped instance sigmaFinite_adelicGLHaar : SigmaFinite (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := by
  haveI : (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
  exact sigmaFinite_of_locallyFinite

private theorem countable_globalPoints_range : Countable (globalPoints (𝓞 ℚ) ℚ).range := by
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℚ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℚ))
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 2) ℚ) :=
    Function.Injective.countable
      (f := (Units.val : Matrix.GeneralLinearGroup (Fin 2) ℚ → Matrix (Fin 2) (Fin 2) ℚ)) fun _ _ hab => Units.ext hab
  exact (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 ℚ) ℚ)).countable

private theorem measurePreserving_mul_left_restrict_detSlab (e₁ e₂ : ℝ) {g : AdelicGL2 (𝓞 ℚ) ℚ}
    (hg : ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) = 1) :
    MeasurePreserving (fun x : AdelicGL2 (𝓞 ℚ) ℚ => g * x) ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂))
      ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂)) := by
  haveI : (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
  have hmeas : Measurable fun x : AdelicGL2 (𝓞 ℚ) ℚ => g * x := measurable_const_mul g
  refine ⟨hmeas, Measure.ext fun t ht => ?_⟩
  rw [Measure.map_apply hmeas ht, Measure.restrict_apply (hmeas ht), Measure.restrict_apply ht]
  have hinter : (fun x => g * x) ⁻¹' t ∩ detSlab e₁ e₂ = (fun x => g * x) ⁻¹' (t ∩ detSlab e₁ e₂) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, mul_mem_detSlab_iff e₁ e₂ hg]
  rw [hinter]
  exact measure_preimage_mul _ _ _

private theorem smulInvariantMeasure_globalPoints_range_restrict_detSlab (e₁ e₂ : ℝ) :
    SMulInvariantMeasure (globalPoints (𝓞 ℚ) ℚ).range (AdelicGL2 (𝓞 ℚ) ℚ)
      ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂)) := by
  refine ⟨fun c t ht => ?_⟩
  obtain ⟨c, γ, rfl⟩ := c
  exact (measurePreserving_mul_left_restrict_detSlab e₁ e₂ (ideleNorm_det_globalPoints γ)).measure_preimage
    ht.nullMeasurableSet

private theorem smulInvariantMeasure_range_comp_unipotentGL2Hom_restrict_detSlab (e₁ e₂ : ℝ) :
    SMulInvariantMeasure ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range (AdelicGL2 (𝓞 ℚ) ℚ)
      ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂)) := by
  refine ⟨fun c t ht => ?_⟩
  obtain ⟨c, b, rfl⟩ := c
  exact (measurePreserving_mul_left_restrict_detSlab e₁ e₂
    (ideleNorm_det_globalPoints (unipotentGL2Hom (R := ℚ) b))).measure_preimage ht.nullMeasurableSet

private theorem coversModCentre_iUnion_singleton_one :
    CoversModCentre ℚ (⋃ x ∈ ({1} : Finset (AdelicGL2 (𝓞 ℚ) ℚ)),
      (· * x) '' centreCutSiegelSet ℚ (Real.sqrt 3 / 2) (1 / 2) 1 2) := by
  intro g
  obtain ⟨γ, z, h⟩ := centreCutSiegelSet_coversModCentre_rat le_rfl le_rfl two_pos one_le_two g
  exact ⟨γ, z, Set.mem_iUnion₂.mpr ⟨1, Finset.mem_singleton_self 1, ⟨_, h, mul_one _⟩⟩⟩

private
theorem exists_isFundamentalDomain_rationalUnipotent_restrict_detSlab {e₁ e₂ : ℝ} (he₁ : 0 < e₁) (he : e₁ < e₂) :
    ∃ F : Set (AdelicGL2 (𝓞 ℚ) ℚ),
      IsFundamentalDomain ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range F
        ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂)) := by
  haveI : MeasurableConstSMul (AdelicGL2 (𝓞 ℚ) ℚ) (AdelicGL2 (𝓞 ℚ) ℚ) := ⟨fun c => measurable_const_mul c⟩
  haveI := countable_globalPoints_range
  haveI := smulInvariantMeasure_globalPoints_range_restrict_detSlab e₁ e₂
  obtain ⟨_, _, _, 𝓕, _, _, _, h𝓕, _⟩ :=
    exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre ℚ
      (Real.sqrt 3 / 2) (1 / 2) 1 2 {1} (by positivity) one_pos one_lt_two coversModCentre_iUnion_singleton_one
      e₁ e₂ he₁ he
  have hle : ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range ≤ (globalPoints (𝓞 ℚ) ℚ).range := by
    rintro _ ⟨k, rfl⟩
    exact ⟨_, rfl⟩
  exact ⟨_, isFundamentalDomain_iUnion_out_smul h𝓕 (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    fun _ _ => rfl⟩

private theorem globalPoints_unipotentGL2 (β : ℚ) :
    globalPoints (𝓞 ℚ) ℚ (unipotentGL2 β) = unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [globalPoints, Matrix.GeneralLinearGroup.map_apply]
  fin_cases i <;> fin_cases j <;> simp [unipotentGL2]

private theorem unipotentGL2_mul_comm (t s : AdeleRing (𝓞 ℚ) ℚ) :
    unipotentGL2 t * unipotentGL2 s = unipotentGL2 s * unipotentGL2 t := by
  rw [← unipotentGL2_add, ← unipotentGL2_add, add_comm]

private theorem exists_eq_globalPoints_unipotentGL2
    (γ : ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range) :
    ∃ β : ℚ, (γ : AdelicGL2 (𝓞 ℚ) ℚ) = globalPoints (𝓞 ℚ) ℚ (unipotentGL2 β) := by
  obtain ⟨b, hb⟩ := γ.2
  exact ⟨Multiplicative.toAdd b, hb.symm⟩

private theorem isFundamentalDomain_image_unipotentGL2_mul {e₁ e₂ : ℝ} {F : Set (AdelicGL2 (𝓞 ℚ) ℚ)}
    (hF : IsFundamentalDomain ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range F
      ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂))) (t : AdeleRing (𝓞 ℚ) ℚ) :
    IsFundamentalDomain ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range
      ((fun x => unipotentGL2 t * x) '' F) ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂)) := by
  refine hF.image_of_equiv (Equiv.mulLeft (unipotentGL2 t)) ?_ (Equiv.refl _) fun γ x => ?_
  · rw [Equiv.mulLeft_symm]
    exact (measurePreserving_mul_left_restrict_detSlab e₁ e₂
      (ideleNorm_det_inv_eq_one (ideleNorm_det_unipotentGL2 t))).quasiMeasurePreserving
  · obtain ⟨β, hβ⟩ := exists_eq_globalPoints_unipotentGL2 γ
    show unipotentGL2 t * ((γ : AdelicGL2 (𝓞 ℚ) ℚ) * x) = (γ : AdelicGL2 (𝓞 ℚ) ℚ) * (unipotentGL2 t * x)
    rw [hβ, globalPoints_unipotentGL2, ← mul_assoc, ← mul_assoc, unipotentGL2_mul_comm]

private theorem injective_globalPoints_comp_unipotentGL2Hom :
    Function.Injective ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))) := by
  intro b₁ b₂ hb
  have h1 : ∀ b : Multiplicative ℚ, ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))) b
      = unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (Multiplicative.toAdd b)) := fun b =>
    globalPoints_unipotentGL2 (Multiplicative.toAdd b)
  rw [h1, h1] at hb
  have h2 := congrArg (fun u : AdelicGL2 (𝓞 ℚ) ℚ => (u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 0 1) hb
  simp only [unipotentGL2] at h2
  haveI : Nontrivial (InfiniteAdeleRing ℚ) := inferInstanceAs (Nontrivial ((v : InfinitePlace ℚ) → v.Completion))
  haveI : Nontrivial (AdeleRing (𝓞 ℚ) ℚ) :=
    inferInstanceAs (Nontrivial (InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ))
  exact Multiplicative.toAdd.injective ((algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)).injective (by simpa using h2))

private noncomputable def rationalUnipotentEquiv :
    ℚ ≃ ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range :=
  Multiplicative.ofAdd.trans (MonoidHom.ofInjective injective_globalPoints_comp_unipotentGL2Hom).toEquiv

private theorem coe_rationalUnipotentEquiv (β : ℚ) :
    ((rationalUnipotentEquiv β : ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range) :
      AdelicGL2 (𝓞 ℚ) ℚ) = unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) := by
  show (((MonoidHom.ofInjective injective_globalPoints_comp_unipotentGL2Hom) (Multiplicative.ofAdd β) :
    ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range) : AdelicGL2 (𝓞 ℚ) ℚ) = _
  rw [MonoidHom.ofInjective_apply]
  exact globalPoints_unipotentGL2 β

private theorem setIntegral_mul_eq_zero_of_isCuspidalFn (h : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hleft : ∀ (β : ℚ) (y : AdelicGL2 (𝓞 ℚ) ℚ), h (globalPoints (𝓞 ℚ) ℚ (unipotentGL2 β) * y) = h y)
    (hcusp : @IsCuspidalFn _ (adeleBorel (𝓞 ℚ) ℚ) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 ℚ) ℚ) (adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
      unipotentGL2 h)
    (A : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hA : ∀ (t : AdeleRing (𝓞 ℚ) ℚ) (y : AdelicGL2 (𝓞 ℚ) ℚ), A (unipotentGL2 t * y) = A y)
    {e₁ e₂ : ℝ} {F : Set (AdelicGL2 (𝓞 ℚ) ℚ)}
    (hF : IsFundamentalDomain ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range F
      ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂)))
    (hint : Integrable
      (Function.uncurry fun (t : AdeleRing (𝓞 ℚ) ℚ) (y : AdelicGL2 (𝓞 ℚ) ℚ) => h (unipotentGL2 t * y) * A y)
      ((@ProbabilityTheory.cond _ (adeleBorel (𝓞 ℚ) ℚ) (adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)).prod
        (((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂)).restrict F))) :
    ∫ y in F, h y * A y ∂((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂)) = 0 := by
  haveI := AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ
  set ν := @ProbabilityTheory.cond _ (adeleBorel (𝓞 ℚ) ℚ) (adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ) with hν
  haveI : Countable ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range :=
    rationalUnipotentEquiv.symm.injective.countable
  haveI := smulInvariantMeasure_range_comp_unipotentGL2Hom_restrict_detSlab e₁ e₂
  haveI : SFinite ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂)) := inferInstance
  set μ' := (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂) with hμ'

  have hinv : ∀ (γ : ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range) (y : AdelicGL2 (𝓞 ℚ) ℚ),
      h (γ • y) * A (γ • y) = h y * A y := by
    intro γ y
    obtain ⟨β, hβ⟩ := exists_eq_globalPoints_unipotentGL2 γ
    show h ((γ : AdelicGL2 (𝓞 ℚ) ℚ) * y) * A ((γ : AdelicGL2 (𝓞 ℚ) ℚ) * y) = h y * A y
    rw [hβ, hleft, globalPoints_unipotentGL2, hA]

  have hshift : ∀ t : AdeleRing (𝓞 ℚ) ℚ,
      ∫ y in F, h y * A y ∂μ' = ∫ y in F, h (unipotentGL2 t * y) * A y ∂μ' := by
    intro t
    calc ∫ y in F, h y * A y ∂μ'
        = ∫ y in (fun x => unipotentGL2 t * x) '' F, h y * A y ∂μ' :=
          hF.setIntegral_eq (isFundamentalDomain_image_unipotentGL2_mul hF t) hinv
      _ = ∫ y in F, h (unipotentGL2 t * y) * A (unipotentGL2 t * y) ∂μ' :=
          (measurePreserving_mul_left_restrict_detSlab e₁ e₂ (ideleNorm_det_unipotentGL2 t)).setIntegral_image_emb
            (MeasurableEquiv.mulLeft (unipotentGL2 t)).measurableEmbedding _ _
      _ = ∫ y in F, h (unipotentGL2 t * y) * A y ∂μ' := by simp only [hA]

  have hinner : ∀ y : AdelicGL2 (𝓞 ℚ) ℚ, ∫ t, h (unipotentGL2 t * y) * A y ∂ν = 0 := by
    intro y
    rw [integral_mul_const]
    have hy : ∫ t, h (unipotentGL2 t * y) ∂ν = 0 := hcusp y
    rw [hy, zero_mul]
  calc ∫ y in F, h y * A y ∂μ' = ∫ t, (∫ y in F, h y * A y ∂μ') ∂ν := by
        rw [integral_const, probReal_univ, one_smul]
    _ = ∫ t, ∫ y in F, h (unipotentGL2 t * y) * A y ∂μ' ∂ν := integral_congr_ae (Filter.Eventually.of_forall hshift)
    _ = ∫ y in F, ∫ t, h (unipotentGL2 t * y) * A y ∂ν ∂μ' := integral_integral_swap hint
    _ = 0 := by simp only [hinner, integral_zero]

private theorem rightConv_eq_integral_mul (h f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    rightConv ℚ h f g = ∫ z, h z * f (g⁻¹ * z) ∂(adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := by
  haveI : (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
  rw [rightConv_apply]
  show ∫ x, h (g * x) * f x ∂(adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) = _
  rw [← integral_mul_left_eq_self (fun z => h z * f (g⁻¹ * z)) g]
  simp only [inv_mul_cancel_left]

private theorem rightConv_eq_setIntegral_mul_tsum (h f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hcont : Continuous h)
    (hleft : ∀ (β : ℚ) (y : AdelicGL2 (𝓞 ℚ) ℚ), h (globalPoints (𝓞 ℚ) ℚ (unipotentGL2 β) * y) = h y)
    (hfc : Continuous f) (g : AdelicGL2 (𝓞 ℚ) ℚ)
    (hint : Integrable (fun z => h z * f (g⁻¹ * z)) (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
    {e₁ e₂ : ℝ} (hsupp : ∀ z, f (g⁻¹ * z) ≠ 0 → z ∈ detSlab e₁ e₂) {F : Set (AdelicGL2 (𝓞 ℚ) ℚ)}
    (hF : IsFundamentalDomain ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range F
      ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂))) :
    rightConv ℚ h f g = ∫ y in F, h y * ∑' β : ℚ, f (g⁻¹ * unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * y)
      ∂((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂)) := by
  haveI := countable_globalPoints_range
  haveI : Countable ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range :=
    rationalUnipotentEquiv.symm.injective.countable
  haveI := smulInvariantMeasure_range_comp_unipotentGL2Hom_restrict_detSlab e₁ e₂
  haveI : SFinite ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂)) := inferInstance
  set μ' := (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂) with hμ'
  set Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := fun z => h z * f (g⁻¹ * z) with hΦ

  have hterm : ∀ (γ : ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range) (y : AdelicGL2 (𝓞 ℚ) ℚ),
      Φ (γ • y) = h y * f (g⁻¹ * (γ : AdelicGL2 (𝓞 ℚ) ℚ) * y) := by
    intro γ y
    obtain ⟨β, hβ⟩ := exists_eq_globalPoints_unipotentGL2 γ
    show h ((γ : AdelicGL2 (𝓞 ℚ) ℚ) * y) * f (g⁻¹ * ((γ : AdelicGL2 (𝓞 ℚ) ℚ) * y))
      = h y * f (g⁻¹ * (γ : AdelicGL2 (𝓞 ℚ) ℚ) * y)
    rw [mul_assoc, hβ, hleft]

  have hΦint : Integrable Φ μ' := hint.restrict
  have hΦslab : ∫ z, Φ z ∂(adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) = ∫ z, Φ z ∂μ' := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_).symm
    have hz' : f (g⁻¹ * z) = 0 := by
      by_contra hne
      exact hz (hsupp z hne)
    simp only [hΦ, hz', mul_zero]

  have hmeas : ∀ γ : ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range,
      AEStronglyMeasurable (fun y => Φ (γ⁻¹ • y)) (μ'.restrict F) := by
    intro γ
    have hc : Continuous fun y : AdelicGL2 (𝓞 ℚ) ℚ => Φ (γ⁻¹ • y) := by
      have hΦc : Continuous Φ := hcont.mul (hfc.comp (continuous_const.mul continuous_id))
      exact hΦc.comp (continuous_const.mul continuous_id)
    exact hc.aestronglyMeasurable
  have hsum : ∑' γ : ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range,
      ∫⁻ y, ‖Φ (γ⁻¹ • y)‖ₑ ∂(μ'.restrict F) ≠ ⊤ := by
    have h1 := hF.lintegral_eq_tsum' fun z => ‖Φ z‖ₑ
    rw [← h1]
    exact hΦint.hasFiniteIntegral.ne

  calc rightConv ℚ h f g = ∫ z, Φ z ∂μ' := (rightConv_eq_integral_mul h f g).trans hΦslab
    _ = ∑' γ : ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range, ∫ y in F, Φ (γ⁻¹ • y) ∂μ' :=
        hF.integral_eq_tsum' Φ hΦint
    _ = ∫ y in F, ∑' γ : ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range, Φ (γ⁻¹ • y) ∂μ' :=
        (integral_tsum hmeas hsum).symm
    _ = ∫ y in F, ∑' γ : ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range, Φ (γ • y) ∂μ' := by
        congr 1
        funext y
        exact (Equiv.inv _).tsum_eq fun γ => Φ (γ • y)
    _ = ∫ y in F, ∑' β : ℚ, h y * f (g⁻¹ * unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * y) ∂μ' := by
        congr 1
        funext y
        rw [← rationalUnipotentEquiv.tsum_eq fun γ => Φ (γ • y)]
        congr 1
        funext β
        rw [hterm, coe_rationalUnipotentEquiv]
    _ = ∫ y in F, h y * ∑' β : ℚ, f (g⁻¹ * unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * y) ∂μ' := by
        congr 1
        funext y
        exact tsum_mul_left

end Rat
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage"

end AutomorphicForm.GodementEstimate
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm"

end UnipotentDomain
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

section WindowIntegrability

set_option autoImplicit false

p2m_open "MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm~continuous_unipotentGL2 P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm AutomorphicForm.WindowedSiegel"
open scoped ENNReal

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsArithGenuineCuspRealizable CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsIdeleClassChar finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff lsXiMemberAt_iff IsAutomorphicFnAt unipotentGL2 unipotentGL2_coe unipotentGL2_add unipotentGL2Hom IsCuspidalFn HeckeEigensystem.cNorm SmoothCusp.heckeCosetSum SmoothCusp.IsHeckeCosetEigenfunctionAt HeckeEigensystem SiegelCovering.CoversModCentre SiegelCovering.mul_centralScalar_comm IsSlowlyIncreasingOn IsRapidlyDecreasingOn SiegelCovering.centreCutSiegelSet_coversModCentre_rat archHeight_glArch_centralScalar_mul continuous_and_hasCompactSupport_of_isFactorizableTestFn IsFinTestFactor IsFactorizableTestFn continuous_rightConv_and_contDiff_of_isFactorizableTestFn rightConv rightConv_apply rightConv_comp_mul_left exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat IsIsotypicCuspFormAt isotypicCuspSubmodule_ne_bot_iff cuspClasses exists_isIsotypicCuspFormAt_ne_zero_of_mem_cuspClasses exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre exists_mem_cuspClasses_levelOne_of_mem_cuspClasses_principalLevel heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps ideleNorm_det_globalPoints isCuspidalFn_rightConv isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn isKfSmooth_rightConv norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply integralMatrixSet integralMatrixSet_eq_pi isOpen_integralMatrixSet IsLocalTestFn localIntegralSet mem_localIntegralSet isCompact_localIntegralSet isLocallyConstant_indicator_one unitFinSet one_mem_unitFinSet isCompact_unitFinSet isOpen_unitFinSet unitFinSet_eq_finiteIntegralGL2 indicator_unitFinSet_mul_left isBiInvariantUnder_bot IsUnitFactorizableAt"
namespace GodementEstimate
p2m_open "AutomorphicForm~continuous_unipotentGL2"

private
theorem measure_image_mul_right_centreCutSiegelSet_lt_top {c d₁ : ℝ} (hc : 0 < c) (u : ℝ) (hd₁ : 0 < d₁) (d₂ : ℝ)
    (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ ((· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) < ⊤ := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 ℚ) ℚ) := glBorel (Fin 2) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdelicGL2 (𝓞 ℚ) ℚ) := borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ
  haveI : (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
  have hS : MeasurableSet (centreCutSiegelSet ℚ c u d₁ d₂) := measurableSet_centreCutSiegelSet c u d₁ d₂
  rw [Set.image_mul_right, ← Measure.map_apply (measurable_mul_const x⁻¹) hS]
  exact SiegelVolume.measure_centreCutSiegelSet_lt_top ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).map (· * x⁻¹)) hc u hd₁ d₂

private theorem measurableSet_iUnion_image_mul_right_centreCutSiegelSet (c u d₁ d₂ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) :
    @MeasurableSet _ (glBorel (Fin 2) (𝓞 ℚ) ℚ) (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 ℚ) ℚ) := glBorel (Fin 2) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdelicGL2 (𝓞 ℚ) ℚ) := borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ
  have hS : MeasurableSet (centreCutSiegelSet ℚ c u d₁ d₂) := measurableSet_centreCutSiegelSet c u d₁ d₂
  refine T.measurableSet_biUnion fun x _ => ?_
  rw [Set.image_mul_right]
  exact (measurable_mul_const x⁻¹) hS

private theorem measure_iUnion_image_mul_right_centreCutSiegelSet_lt_top {c d₁ : ℝ} (hc : 0 < c) (u : ℝ) (hd₁ : 0 < d₁)
    (d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) :
    adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) < ⊤ :=
  (measure_biUnion_finset_le T _).trans_lt
    (ENNReal.sum_lt_top.mpr fun x _ => measure_image_mul_right_centreCutSiegelSet_lt_top hc u hd₁ d₂ x)

private theorem memLp_two_restrict_iUnion_image_mul_right (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφ : Continuous φ)
    {c d₁ : ℝ} (hc : 0 < c) (u : ℝ) (hd₁ : 0 < d₁) (d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (Bf : AdelicGL2 (𝓞 ℚ) ℚ → ℝ)
    (hB : ∀ x ∈ T, ∀ s ∈ centreCutSiegelSet ℚ c u d₁ d₂, ‖φ (s * x)‖ ≤ Bf x) :
    MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 ℚ) ℚ) := glBorel (Fin 2) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdelicGL2 (𝓞 ℚ) ℚ) := borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ
  have hU := measurableSet_iUnion_image_mul_right_centreCutSiegelSet c u d₁ d₂ T
  haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)) :=
    isFiniteMeasure_restrict.mpr (measure_iUnion_image_mul_right_centreCutSiegelSet_lt_top hc u hd₁ d₂ T).ne
  refine MemLp.of_bound hφ.aestronglyMeasurable (∑ x ∈ T, |Bf x|) ?_
  rw [ae_restrict_iff' hU]
  refine Filter.Eventually.of_forall fun g hg => ?_
  obtain ⟨x, hx, hgx⟩ := Set.mem_iUnion₂.mp hg
  obtain ⟨s, hs, rfl⟩ := hgx
  calc ‖φ (s * x)‖ ≤ Bf x := hB x hx s hs
    _ ≤ |Bf x| := le_abs_self _
    _ ≤ ∑ y ∈ T, |Bf y| := Finset.single_le_sum (fun y _ => abs_nonneg (Bf y)) hx

end AutomorphicForm.GodementEstimate
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end WindowIntegrability
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

section GodementAssembly

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar
p2m_open "AutomorphicForm~continuous_unipotentGL2 P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicHeight"
open scoped Pointwise

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsArithGenuineCuspRealizable CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsIdeleClassChar finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff lsXiMemberAt_iff IsAutomorphicFnAt unipotentGL2 unipotentGL2_coe unipotentGL2_add unipotentGL2Hom IsCuspidalFn HeckeEigensystem.cNorm SmoothCusp.heckeCosetSum SmoothCusp.IsHeckeCosetEigenfunctionAt HeckeEigensystem SiegelCovering.CoversModCentre SiegelCovering.mul_centralScalar_comm IsSlowlyIncreasingOn IsRapidlyDecreasingOn SiegelCovering.centreCutSiegelSet_coversModCentre_rat archHeight_glArch_centralScalar_mul continuous_and_hasCompactSupport_of_isFactorizableTestFn IsFinTestFactor IsFactorizableTestFn continuous_rightConv_and_contDiff_of_isFactorizableTestFn rightConv rightConv_apply rightConv_comp_mul_left exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat IsIsotypicCuspFormAt isotypicCuspSubmodule_ne_bot_iff cuspClasses exists_isIsotypicCuspFormAt_ne_zero_of_mem_cuspClasses exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre exists_mem_cuspClasses_levelOne_of_mem_cuspClasses_principalLevel heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps ideleNorm_det_globalPoints isCuspidalFn_rightConv isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn isKfSmooth_rightConv norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply integralMatrixSet integralMatrixSet_eq_pi isOpen_integralMatrixSet IsLocalTestFn localIntegralSet mem_localIntegralSet isCompact_localIntegralSet isLocallyConstant_indicator_one unitFinSet one_mem_unitFinSet isCompact_unitFinSet isOpen_unitFinSet unitFinSet_eq_finiteIntegralGL2 indicator_unitFinSet_mul_left isBiInvariantUnder_bot IsUnitFactorizableAt"
namespace GodementEstimate
p2m_open "AutomorphicForm~continuous_unipotentGL2"

section Entries

variable {K : Type*} [NormedField K]

private theorem norm_entry_mul_norm_entry_le_rowNormSq (A : Matrix (Fin 2) (Fin 2) K) (k j : Fin 2) :
    ‖A 1 k‖ * ‖A 1 j‖ ≤ rowNormSq A := by
  unfold rowNormSq
  have h0 := norm_nonneg (A 1 0)
  have h1 := norm_nonneg (A 1 1)
  fin_cases k <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    nlinarith [sq_nonneg (‖A 1 0‖ - ‖A 1 1‖)]

private theorem exists_norm_inv_entry_eq (g : GL (Fin 2) K) (i : Fin 2) :
    ∃ k : Fin 2, ‖((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i 0‖
      = ‖(g : Matrix (Fin 2) (Fin 2) K).det‖⁻¹ * ‖(g : Matrix (Fin 2) (Fin 2) K) 1 k‖ := by
  rw [Matrix.coe_units_inv]
  fin_cases i
  · exact ⟨1, by simp [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv', norm_mul, norm_inv]⟩
  · exact ⟨0, by simp [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv', norm_mul, norm_inv]⟩

private theorem norm_inv_entry_mul_entry_le (g : GL (Fin 2) K) (i j : Fin 2) :
    ‖((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i 0 * (g : Matrix (Fin 2) (Fin 2) K) 1 j‖
      ≤ (localHeight g)⁻¹ := by
  obtain ⟨k, hk⟩ := exists_norm_inv_entry_eq g i
  rw [norm_mul, hk, mul_assoc]
  unfold localHeight
  rw [inv_div, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (norm_entry_mul_norm_entry_le_rowNormSq _ k j) (inv_nonneg.mpr (norm_nonneg _))

end Entries
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

section Conjugates

private def boundedIntegralAdeles (R : ℝ) : Set (AdeleRing (𝓞 ℚ) ℚ) :=
  {a | (∀ v : InfinitePlace ℚ, ‖a.1 v‖ ≤ R) ∧ a.2 ∈ integralFiniteAdeles (𝓞 ℚ) ℚ}

private theorem isCompact_boundedIntegralAdeles (R : ℝ) : IsCompact (boundedIntegralAdeles R) := by
  haveI : ∀ v : InfinitePlace ℚ, ProperSpace v.Completion := fun v => AdelicBox.properSpace_completion ℚ v
  have harch : IsCompact {y : InfiniteAdeleRing ℚ | ∀ v, ‖y v‖ ≤ R} := by
    have hpi : {y : InfiniteAdeleRing ℚ | ∀ v, ‖y v‖ ≤ R} =
        Set.pi Set.univ fun v : InfinitePlace ℚ => Metric.closedBall (0 : v.Completion) R := by
      ext y
      exact ⟨fun h v _ => mem_closedBall_zero_iff.mpr (h v),
        fun h v => mem_closedBall_zero_iff.mp (h v (Set.mem_univ v))⟩
    rw [hpi]
    exact isCompact_univ_pi fun v => isCompact_closedBall (0 : v.Completion) R
  have hprod : IsCompact ({y : InfiniteAdeleRing ℚ | ∀ v, ‖y v‖ ≤ R} ×ˢ integralFiniteAdeles (𝓞 ℚ) ℚ) :=
    harch.prod (isCompact_integralFiniteAdeles (𝓞 ℚ) ℚ)
  exact hprod

private
theorem zero_mem_boundedIntegralAdeles {R : ℝ} (hR : 0 ≤ R) : (0 : AdeleRing (𝓞 ℚ) ℚ) ∈ boundedIntegralAdeles R :=
  ⟨fun v => by simpa [show ((0 : AdeleRing (𝓞 ℚ) ℚ).1 v : v.Completion) = 0 from rfl] using hR,
    zero_mem_integralFiniteAdeles⟩

private theorem mul_mem_boundedIntegralAdeles {R₁ R₂ : ℝ} (hR₁ : 0 ≤ R₁) {a b : AdeleRing (𝓞 ℚ) ℚ}
    (ha : a ∈ boundedIntegralAdeles R₁) (hb : b ∈ boundedIntegralAdeles R₂) :
    a * b ∈ boundedIntegralAdeles (R₁ * R₂) :=
  ⟨fun v => by
    change ‖a.1 v * b.1 v‖ ≤ R₁ * R₂
    rw [norm_mul]
    exact mul_le_mul (ha.1 v) (hb.1 v) (norm_nonneg _) hR₁,
   mul_mem_integralFiniteAdeles ha.2 hb.2⟩

private theorem exists_adelicBox_subset_boundedIntegralAdeles :
    ∃ r : ℝ, 0 ≤ r ∧ AdelicBox.adelicBox ℚ ⊆ boundedIntegralAdeles r := by
  obtain ⟨r, hr⟩ := AdelicBox.exists_forall_norm_apply_le_of_mem_infiniteBox ℚ
  refine ⟨|r|, abs_nonneg r, fun t ht => ⟨fun v => (hr t.1 ht.1 v).trans (le_abs_self r), fun v => ht.2 v⟩⟩

private def squareZeroBox (R : ℝ) : Set (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :=
  {M | (∀ i j, M i j ∈ boundedIntegralAdeles R) ∧ M * M = 0}

private theorem isCompact_squareZeroBox (R : ℝ) : IsCompact (squareZeroBox R) := by
  have hbox : IsCompact {M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) | ∀ i j, M i j ∈ boundedIntegralAdeles R} := by
    have hpi : {M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) | ∀ i j, M i j ∈ boundedIntegralAdeles R} =
        Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 => boundedIntegralAdeles R := by
      ext M
      exact ⟨fun hM i _ j _ => hM i j, fun hM i j => hM i (Set.mem_univ i) j (Set.mem_univ j)⟩
    rw [hpi]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_boundedIntegralAdeles R
  have hclosed : IsClosed {M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) | M * M = 0} :=
    isClosed_eq (continuous_id.matrix_mul continuous_id) continuous_const
  have hinter : IsCompact ({M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) | ∀ i j, M i j ∈ boundedIntegralAdeles R}
      ∩ {M | M * M = 0}) := hbox.inter_right hclosed
  exact hinter

private def unitOfSquareZero (R : ℝ) (M : squareZeroBox R) : AdelicGL2 (𝓞 ℚ) ℚ where
  val := 1 + (M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))
  inv := 1 - (M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))
  val_inv := by
    have hM : (M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) * M = 0 := M.2.2
    rw [add_mul, one_mul, mul_sub, mul_one, hM, sub_zero]
    abel
  inv_val := by
    have hM : (M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) * M = 0 := M.2.2
    rw [sub_mul, one_mul, mul_add, mul_one, hM, add_zero]
    abel

private theorem continuous_unitOfSquareZero (R : ℝ) : Continuous (unitOfSquareZero R) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun M : squareZeroBox R => (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) + (M : Matrix _ _ _)
    exact continuous_const.add continuous_subtype_val
  · show Continuous fun M : squareZeroBox R => (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) - (M : Matrix _ _ _)
    exact continuous_const.sub continuous_subtype_val

private theorem isCompact_range_unitOfSquareZero (R : ℝ) : IsCompact (Set.range (unitOfSquareZero R)) := by
  haveI : CompactSpace (squareZeroBox R) := isCompact_iff_compactSpace.mp (isCompact_squareZeroBox R)
  exact isCompact_range (continuous_unitOfSquareZero R)

private def conjMatrix (x : AdelicGL2 (𝓞 ℚ) ℚ) (t : AdeleRing (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) :=
  t • Matrix.vecMulVec (fun i => ((x⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i 0)
    (fun j => (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j)

private theorem conjMatrix_apply (x : AdelicGL2 (𝓞 ℚ) ℚ) (t : AdeleRing (𝓞 ℚ) ℚ) (i j : Fin 2) :
    conjMatrix x t i j = t * (((x⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i 0
      * (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j) := by
  simp [conjMatrix, Matrix.vecMulVec_apply]

private
theorem conjMatrix_mul_self (x : AdelicGL2 (𝓞 ℚ) ℚ) (t : AdeleRing (𝓞 ℚ) ℚ) : conjMatrix x t * conjMatrix x t = 0 := by
  have hdot : (fun j => (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j) ⬝ᵥ
      (fun i => ((x⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i 0) = 0 := by
    have h : ((x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))
        * ((x⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))) 1 0
          = (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0 := by
      rw [Units.mul_inv]
    rw [Matrix.mul_apply] at h
    simpa [dotProduct, Matrix.one_apply] using h
  unfold conjMatrix
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec, hdot, zero_smul]
  ext i j
  simp

private theorem coe_inv_mul_unipotentGL2_mul (x : AdelicGL2 (𝓞 ℚ) ℚ) (t : AdeleRing (𝓞 ℚ) ℚ) :
    ((x⁻¹ * unipotentGL2 t * x : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))
      = 1 + conjMatrix x t := by
  rw [Units.val_mul, Units.val_mul, unipotentGL2_coe]
  have hinv : ((x⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))
      * (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) = 1 := Units.inv_mul x
  ext i j
  fin_cases i <;> fin_cases j
  · have e := congrFun (congrFun hinv 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e
    simp [Matrix.mul_apply, Fin.sum_univ_two, conjMatrix_apply]
    linear_combination e
  · have e := congrFun (congrFun hinv 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e
    simp [Matrix.mul_apply, Fin.sum_univ_two, conjMatrix_apply]
    linear_combination e
  · have e := congrFun (congrFun hinv 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e
    simp [Matrix.mul_apply, Fin.sum_univ_two, conjMatrix_apply]
    linear_combination e
  · have e := congrFun (congrFun hinv 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e
    simp [Matrix.mul_apply, Fin.sum_univ_two, conjMatrix_apply]
    linear_combination e

private theorem archComponent_glArch_apply (x : AdelicGL2 (𝓞 ℚ) ℚ) (v : InfinitePlace ℚ) (i j : Fin 2) :
    (archComponent ℚ v (glArch (𝓞 ℚ) ℚ x) : Matrix (Fin 2) (Fin 2) v.Completion) i j
      = ((x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 v := rfl

private theorem inv_entry_mul_entry_mem_boundedIntegralAdeles {c u d₁ d₂ : ℝ} (hc : 0 < c) {x : AdelicGL2 (𝓞 ℚ) ℚ}
    (hx : x ∈ centreCutSiegelSet ℚ c u d₁ d₂) (i j : Fin 2) :
    ((x⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i 0
        * (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j ∈ boundedIntegralAdeles c⁻¹ := by
  obtain ⟨hfin, hfloor, -, -⟩ := hx
  refine ⟨fun v => ?_, ?_⟩
  · have harch : (archComponent ℚ v (glArch (𝓞 ℚ) ℚ x))⁻¹ = archComponent ℚ v (glArch (𝓞 ℚ) ℚ x⁻¹) := by
      rw [map_inv (glArch (𝓞 ℚ) ℚ) x, map_inv (archComponent ℚ v) (glArch (𝓞 ℚ) ℚ x)]
    have hle := norm_inv_entry_mul_entry_le (archComponent ℚ v (glArch (𝓞 ℚ) ℚ x)) i j
    rw [harch, archComponent_glArch_apply, archComponent_glArch_apply] at hle
    change ‖(((x⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i 0).1 v
      * ((x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).1 v‖ ≤ c⁻¹
    exact hle.trans (inv_anti₀ hc (hfloor v))
  · obtain ⟨hent, hinv⟩ := mem_finiteIntegralGL2_iff.mp hfin
    have h₁ : (((x⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i 0).2
        ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
      have := hinv i 0
      rwa [← map_inv (glFin (𝓞 ℚ) ℚ) x, glFin_apply] at this
    have h₂ : ((x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2 ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
      have := hent 1 j
      rwa [glFin_apply] at this
    exact mul_mem_integralFiniteAdeles h₁ h₂

private theorem exists_isCompact_forall_inv_mul_unipotentGL2_mul_mem (c u d₁ d₂ : ℝ) (hc : 0 < c) :
    ∃ C₀ : Set (AdelicGL2 (𝓞 ℚ) ℚ), IsCompact C₀ ∧ (1 : AdelicGL2 (𝓞 ℚ) ℚ) ∈ C₀ ∧
      ∀ x ∈ centreCutSiegelSet ℚ c u d₁ d₂, ∀ t ∈ AdelicBox.adelicBox ℚ, x⁻¹ * unipotentGL2 t * x ∈ C₀ := by
  obtain ⟨r, hr, hbox⟩ := exists_adelicBox_subset_boundedIntegralAdeles
  refine ⟨Set.range (unitOfSquareZero (r * c⁻¹)), isCompact_range_unitOfSquareZero _, ?_, fun x hx t ht => ?_⟩
  · refine ⟨⟨0, fun i j => zero_mem_boundedIntegralAdeles (mul_nonneg hr (inv_nonneg.mpr hc.le)), by simp⟩, ?_⟩
    exact Units.ext (add_zero (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)))
  · refine ⟨⟨conjMatrix x t, fun i j => ?_, conjMatrix_mul_self x t⟩, ?_⟩
    · rw [conjMatrix_apply]
      exact mul_mem_boundedIntegralAdeles hr (hbox ht) (inv_entry_mul_entry_mem_boundedIntegralAdeles hc hx i j)
    · exact Units.ext (by rw [coe_inv_mul_unipotentGL2_mul]; rfl)

end Conjugates
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

section Tiling

variable {Γ X : Type*} [Group Γ] [Countable Γ] [MulAction Γ X] [MeasurableSpace X] [MeasurableConstSMul Γ X]
  {μ : Measure X} [SMulInvariantMeasure Γ X μ]

private theorem measure_inter_iUnion_smul_le {s : Set X} (hs : IsFundamentalDomain Γ s μ) (t : Set X) :
    μ (s ∩ ⋃ γ : Γ, γ • t) ≤ μ t := by
  rw [Set.inter_iUnion]
  calc μ (⋃ γ : Γ, s ∩ γ • t) ≤ ∑' γ : Γ, μ (s ∩ γ • t) := measure_iUnion_le _
    _ = ∑' γ : Γ, μ (γ • t ∩ s) := tsum_congr fun γ => by rw [Set.inter_comm]
    _ = μ t := (hs.measure_eq_tsum t).symm

end Tiling
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

section TilingRat

private theorem adelicGLHaar_image_mul_left (x : AdelicGL2 (𝓞 ℚ) ℚ) (C : Set (AdelicGL2 (𝓞 ℚ) ℚ)) :
    adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ ((x * ·) '' C) = adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ C := by
  haveI : (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
  rw [Set.image_mul_left]
  exact measure_preimage_mul _ _ _

private theorem adelicGLHaar_lt_top_of_isCompact {C : Set (AdelicGL2 (𝓞 ℚ) ℚ)} (hC : IsCompact C) :
    adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ C < ⊤ := by
  haveI : (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
  exact hC.measure_lt_top

private theorem measure_restrict_detSlab_inter_iUnion_smul_image_le {e₁ e₂ : ℝ} {F : Set (AdelicGL2 (𝓞 ℚ) ℚ)}
    (hF : IsFundamentalDomain ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range F
      ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂)))
    (x : AdelicGL2 (𝓞 ℚ) ℚ) (C : Set (AdelicGL2 (𝓞 ℚ) ℚ)) :
    (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂)
        (F ∩ ⋃ γ : ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range, γ • ((x * ·) '' C))
      ≤ adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ C := by
  haveI : MeasurableConstSMul ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range (AdelicGL2 (𝓞 ℚ) ℚ) :=
    ⟨fun γ => measurable_const_mul (γ : AdelicGL2 (𝓞 ℚ) ℚ)⟩
  haveI : Countable ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range :=
    rationalUnipotentEquiv.symm.injective.countable
  haveI := smulInvariantMeasure_range_comp_unipotentGL2Hom_restrict_detSlab e₁ e₂
  calc (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂)
        (F ∩ ⋃ γ : ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range, γ • ((x * ·) '' C))
      ≤ (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂) ((x * ·) '' C) :=
        measure_inter_iUnion_smul_le hF _
    _ ≤ adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ ((x * ·) '' C) := Measure.le_iff'.1 Measure.restrict_le_self _
    _ = adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ C := adelicGLHaar_image_mul_left x C

end TilingRat
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

section HighPartFurniture

private abbrev rationalUnipotents : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ) :=
  ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range

private def saturatedTranslate (x : AdelicGL2 (𝓞 ℚ) ℚ) (C : Set (AdelicGL2 (𝓞 ℚ) ℚ)) : Set (AdelicGL2 (𝓞 ℚ) ℚ) :=
  ⋃ γ : rationalUnipotents, γ • ((x * ·) '' C)

private theorem saturatedTranslate_mono (x : AdelicGL2 (𝓞 ℚ) ℚ) {C C' : Set (AdelicGL2 (𝓞 ℚ) ℚ)} (hCC' : C ⊆ C') :
    saturatedTranslate x C ⊆ saturatedTranslate x C' :=
  Set.iUnion_mono fun _ => Set.smul_set_mono (Set.image_mono hCC')

private theorem mem_saturatedTranslate_of_rational {x : AdelicGL2 (𝓞 ℚ) ℚ} {C : Set (AdelicGL2 (𝓞 ℚ) ℚ)} (β : ℚ)
    {y : AdelicGL2 (𝓞 ℚ) ℚ} (hy : x⁻¹ * unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * y ∈ C) :
    y ∈ saturatedTranslate x C := by
  refine Set.mem_iUnion.mpr ⟨(rationalUnipotentEquiv β)⁻¹, ?_⟩
  refine Set.mem_smul_set.mpr
    ⟨x * (x⁻¹ * unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * y), ⟨_, hy, rfl⟩, ?_⟩
  rw [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_inv, coe_rationalUnipotentEquiv]
  group

private theorem mem_saturatedTranslate_of_tsum_ne_zero (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (x y : AdelicGL2 (𝓞 ℚ) ℚ)
    (hne : (∑' β : ℚ, f (x⁻¹ * unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * y)) ≠ 0) :
    y ∈ saturatedTranslate x (tsupport f) := by
  by_contra hy
  apply hne
  have hterm : ∀ β : ℚ, f (x⁻¹ * unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * y) = 0 := fun β => by
    by_contra hβ
    exact hy (mem_saturatedTranslate_of_rational β (subset_tsupport f hβ))
  simp only [hterm, tsum_zero]

private theorem norm_le_of_mem_saturatedTranslate (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hinv : ∀ (β : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * g) = φ g)
    {x : AdelicGL2 (𝓞 ℚ) ℚ} {C : Set (AdelicGL2 (𝓞 ℚ) ℚ)} {b : ℝ} (hb : ∀ s ∈ C, ‖φ (x * s)‖ ≤ b)
    {y : AdelicGL2 (𝓞 ℚ) ℚ} (hy : y ∈ saturatedTranslate x C) : ‖φ y‖ ≤ b := by
  obtain ⟨γ, hγ⟩ := Set.mem_iUnion.mp hy
  obtain ⟨z, ⟨s, hs, rfl⟩, rfl⟩ := Set.mem_smul_set.mp hγ
  obtain ⟨β, hβ⟩ := exists_eq_globalPoints_unipotentGL2 γ
  rw [Subgroup.smul_def, smul_eq_mul, hβ, globalPoints_unipotentGL2, hinv]
  exact hb s hs

private theorem unipotentGL2_algebraMap_mul_invariant (h : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      h (globalPoints (𝓞 ℚ) ℚ γ * g) = h g)
    (β : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ) : h (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * g) = h g := by
  rw [← globalPoints_unipotentGL2]
  exact hleft _ _

private theorem subset_mul_left_of_one_mem {C₀ : Set (AdelicGL2 (𝓞 ℚ) ℚ)} (h₁ : (1 : AdelicGL2 (𝓞 ℚ) ℚ) ∈ C₀)
    (C : Set (AdelicGL2 (𝓞 ℚ) ℚ)) : C ⊆ C₀ * C := fun s hs => by
  simpa using Set.mul_mem_mul h₁ hs

private theorem isCompact_smul_image_mul (γ : rationalUnipotents) (x : AdelicGL2 (𝓞 ℚ) ℚ) {C : Set (AdelicGL2 (𝓞 ℚ) ℚ)}
    (hC : IsCompact C) : IsCompact (γ • ((x * ·) '' C)) := by
  rw [← Set.image_smul]
  exact (hC.image (continuous_const_mul x)).image (continuous_const_mul (γ : AdelicGL2 (𝓞 ℚ) ℚ))

private
theorem measurableSet_saturatedTranslate (x : AdelicGL2 (𝓞 ℚ) ℚ) {C : Set (AdelicGL2 (𝓞 ℚ) ℚ)} (hC : IsCompact C) :
    MeasurableSet (saturatedTranslate x C) := by
  haveI : Countable rationalUnipotents := rationalUnipotentEquiv.symm.injective.countable
  exact MeasurableSet.iUnion fun γ => (isCompact_smul_image_mul γ x hC).isClosed.measurableSet

private theorem unipotentGL2_mul_mem_saturatedTranslate {x : AdelicGL2 (𝓞 ℚ) ℚ} {C₀ C : Set (AdelicGL2 (𝓞 ℚ) ℚ)}
    {t : AdeleRing (𝓞 ℚ) ℚ} (ht : x⁻¹ * unipotentGL2 t * x ∈ C₀) {y : AdelicGL2 (𝓞 ℚ) ℚ}
    (hy : y ∈ saturatedTranslate x C) : unipotentGL2 t * y ∈ saturatedTranslate x (C₀ * C) := by
  obtain ⟨γ, hγ⟩ := Set.mem_iUnion.mp hy
  obtain ⟨z, ⟨s, hs, rfl⟩, rfl⟩ := Set.mem_smul_set.mp hγ
  obtain ⟨β, hβ⟩ := exists_eq_globalPoints_unipotentGL2 γ
  refine Set.mem_iUnion.mpr ⟨γ, Set.mem_smul_set.mpr
    ⟨x * ((x⁻¹ * unipotentGL2 t * x) * s), ⟨_, Set.mul_mem_mul ht hs, rfl⟩, ?_⟩⟩
  have hcomm : globalPoints (𝓞 ℚ) ℚ (unipotentGL2 β) * unipotentGL2 t
      = unipotentGL2 t * globalPoints (𝓞 ℚ) ℚ (unipotentGL2 β) := by
    rw [globalPoints_unipotentGL2, ← unipotentGL2_add, ← unipotentGL2_add, add_comm]
  simp only [Subgroup.smul_def, smul_eq_mul, hβ, mul_assoc, mul_inv_cancel_left]
  rw [← mul_assoc, hcomm, mul_assoc]

private theorem mem_saturatedTranslate_mul_of_inv_mul_unipotentGL2_mul_mem {x : AdelicGL2 (𝓞 ℚ) ℚ}
    {C₀ : Set (AdelicGL2 (𝓞 ℚ) ℚ)} (hC₀ : ∀ t ∈ AdelicBox.adelicBox ℚ, x⁻¹ * unipotentGL2 t * x ∈ C₀)
    {C : Set (AdelicGL2 (𝓞 ℚ) ℚ)} {t : AdeleRing (𝓞 ℚ) ℚ} {y : AdelicGL2 (𝓞 ℚ) ℚ}
    (hz : x⁻¹ * unipotentGL2 t * y ∈ C) : y ∈ saturatedTranslate x (C₀ * C) := by
  obtain ⟨β, hβ⟩ := (AdelicBox.existsUnique_algebraMap_add_mem_adelicBox ℚ (-t)).exists
  refine mem_saturatedTranslate_of_rational β ?_
  have hsplit : unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β)
      = unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + -t) * unipotentGL2 t := by
    rw [← unipotentGL2_add, neg_add_cancel_right]
  have hkey : x⁻¹ * unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * y
      = (x⁻¹ * unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + -t) * x) * (x⁻¹ * unipotentGL2 t * y) := by
    rw [hsplit]
    simp only [mul_assoc, mul_inv_cancel_left]
  rw [hkey]
  exact Set.mul_mem_mul (hC₀ _ hβ) hz

private theorem measure_restrict_detSlab_inter_saturatedTranslate_le {e₁ e₂ : ℝ} {F : Set (AdelicGL2 (𝓞 ℚ) ℚ)}
    (hF : IsFundamentalDomain ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range F
      ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂)))
    (x : AdelicGL2 (𝓞 ℚ) ℚ) (C : Set (AdelicGL2 (𝓞 ℚ) ℚ)) :
    (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂) (F ∩ saturatedTranslate x C)
      ≤ adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ C :=
  measure_restrict_detSlab_inter_iUnion_smul_image_le hF x C

private theorem exists_detSlab_forall_mem {c u d₁ d₂ : ℝ} (hd₁ : 0 < d₁) {C : Set (AdelicGL2 (𝓞 ℚ) ℚ)}
    (hC : IsCompact C) :
    ∃ e₁ e₂ : ℝ, 0 < e₁ ∧ e₁ < e₂ ∧
      ∀ x ∈ centreCutSiegelSet ℚ c u d₁ d₂, ∀ z : AdelicGL2 (𝓞 ℚ) ℚ, x⁻¹ * z ∈ C → z ∈ detSlab e₁ e₂ := by
  obtain ⟨m, M, hm, hCm⟩ := exists_ideleNorm_det_bounds C hC
  refine ⟨d₁ * m, max (d₂ * M) (d₁ * m) + 1, mul_pos hd₁ hm,
    by linarith [le_max_right (d₂ * M) (d₁ * m)], fun x hx z hz => ?_⟩
  obtain ⟨hx₁, hx₂⟩ := ideleNorm_det_mem_Icc_of_mem_centreCutSiegelSet hx
  obtain ⟨hz₁, hz₂⟩ := hCm _ hz
  have hsplit : NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det z)
      = NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det x)
        * NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (x⁻¹ * z)) := by
    rw [← NumberField.TateGlobal.ideleNorm_mul, ← map_mul, mul_inv_cancel_left]
  have hx0 : 0 ≤ NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det x) := hd₁.le.trans hx₁
  refine ⟨?_, ?_⟩
  · rw [hsplit]
    exact mul_le_mul hx₁ hz₁ hm.le hx0
  · rw [hsplit]
    refine (mul_le_mul hx₂ hz₂ (hm.le.trans hz₁) (hx0.trans hx₂)).trans ?_
    linarith [le_max_left (d₂ * M) (d₁ * m)]

private theorem integrable_mul_comp_inv_mul {h f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hcont : Continuous h) (hfc : Continuous f)
    (hfs : HasCompactSupport f) (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    Integrable (fun z => h z * f (x⁻¹ * z)) (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := by
  haveI : (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
  have hsupp : HasCompactSupport fun z => f (x⁻¹ * z) := hfs.comp_homeomorph (Homeomorph.mulLeft x⁻¹)
  have hsupp' : HasCompactSupport fun z => h z * f (x⁻¹ * z) := hsupp.mul_left
  exact (hcont.mul (hfc.comp (continuous_const_mul x⁻¹))).integrable_of_hasCompactSupport hsupp'

end HighPartFurniture
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

section BoundedIntegrability

private theorem integrable_of_support_subset_of_bounded {ν : Measure (AdelicGL2 (𝓞 ℚ) ℚ)} [SFinite ν]
    {S : Set (AdelicGL2 (𝓞 ℚ) ℚ)}
    (hS : MeasurableSet S) (hSfin : ν S ≠ ⊤) {g : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hg : AEStronglyMeasurable g ν)
    (hsupp : ∀ y, g y ≠ 0 → y ∈ S) {b : ℝ} (hb : ∀ y ∈ S, ‖g y‖ ≤ b) : Integrable g ν := by
  rw [← integrableOn_iff_integrable_of_support_subset fun y hy => hsupp y hy]
  haveI : IsFiniteMeasure (ν.restrict S) := isFiniteMeasure_restrict.mpr hSfin
  refine Integrable.mono' (integrable_const b) hg.restrict ?_
  exact (ae_restrict_mem hS).mono fun y hy => hb y hy

private
theorem integrable_uncurry_mul_of_bounded {ν : Measure (AdelicGL2 (𝓞 ℚ) ℚ)} [SFinite ν] {S : Set (AdelicGL2 (𝓞 ℚ) ℚ)}
    (hS : MeasurableSet S) (hSfin : ν S ≠ ⊤) {h : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hcont : Continuous h)
    {A : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hA : AEStronglyMeasurable A ν) (hAsupp : ∀ y, A y ≠ 0 → y ∈ S) {b₁ b₂ : ℝ}
    (hb₁0 : 0 ≤ b₁) (hb₁ : ∀ t ∈ AdelicBox.adelicBox ℚ, ∀ y ∈ S, ‖h (unipotentGL2 t * y)‖ ≤ b₁)
    (hb₂ : ∀ y ∈ S, ‖A y‖ ≤ b₂) :
    Integrable
      (Function.uncurry fun (t : AdeleRing (𝓞 ℚ) ℚ) (y : AdelicGL2 (𝓞 ℚ) ℚ) => h (unipotentGL2 t * y) * A y)
      ((@ProbabilityTheory.cond _ (adeleBorel (𝓞 ℚ) ℚ) (adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)).prod ν) := by
  haveI : IsProbabilityMeasure
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 ℚ) ℚ) (adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)) :=
    AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ
  haveI : IsFiniteMeasure (ν.restrict S) := isFiniteMeasure_restrict.mpr hSfin
  have hsupp : Function.support
      (Function.uncurry fun (t : AdeleRing (𝓞 ℚ) ℚ) (y : AdelicGL2 (𝓞 ℚ) ℚ) => h (unipotentGL2 t * y) * A y)
        ⊆ Set.univ ×ˢ S := by
    intro p hp
    refine ⟨Set.mem_univ _, hAsupp p.2 fun hA0 => Function.mem_support.mp hp ?_⟩
    show h (unipotentGL2 p.1 * p.2) * A p.2 = 0
    rw [hA0, mul_zero]
  rw [← integrableOn_iff_integrable_of_support_subset hsupp, IntegrableOn, ← Measure.prod_restrict,
    Measure.restrict_univ]
  have hmeas : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdelicGL2 (𝓞 ℚ) ℚ => h (unipotentGL2 p.1 * p.2) :=
    hcont.comp ((UnipotentAverage.continuous_unipotentGL2.comp continuous_fst).mul continuous_snd)
  refine Integrable.mono' (integrable_const (b₁ * b₂))
    (hmeas.aestronglyMeasurable.mul (hA.restrict.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd))
    ?_
  have hbox : ∀ᵐ t ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 ℚ) ℚ) (adelicAddHaar (𝓞 ℚ) ℚ)
      (AdelicBox.adelicBox ℚ)), t ∈ AdelicBox.adelicBox ℚ :=
    ProbabilityTheory.ae_cond_mem (AdelicBox.measurableSet_adelicBox ℚ)
  have hmem : ∀ᵐ p ∂((@ProbabilityTheory.cond _ (adeleBorel (𝓞 ℚ) ℚ) (adelicAddHaar (𝓞 ℚ) ℚ)
      (AdelicBox.adelicBox ℚ)).prod (ν.restrict S)), p ∈ AdelicBox.adelicBox ℚ ×ˢ S :=
    (Measure.ae_prod_mem_iff_ae_ae_mem ((AdelicBox.measurableSet_adelicBox ℚ).prod hS)).mpr
      (hbox.mono fun t ht => (ae_restrict_mem hS).mono fun y hy => ⟨ht, hy⟩)
  refine hmem.mono fun p hp => ?_
  show ‖h (unipotentGL2 p.1 * p.2) * A p.2‖ ≤ b₁ * b₂
  rw [norm_mul]
  exact mul_le_mul (hb₁ p.1 hp.1 p.2 hp.2) (hb₂ p.2 hp.2) (norm_nonneg _) hb₁0

end BoundedIntegrability
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

section HighPart

private theorem exists_forall_norm_rightConv_le_of_one_le_adelicHeight
    (h : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hcont : Continuous h)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      h (globalPoints (𝓞 ℚ) ℚ γ * g) = h g)
    (hcentral : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      h (centralScalar (𝓞 ℚ) ℚ z * g) = ((ξ z : ℂˣ) : ℂ) * h g)
    (hcusp : @IsCuspidalFn _ (adeleBorel (𝓞 ℚ) ℚ) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 ℚ) ℚ) (adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
      unipotentGL2 h)
    (hgrowth : ∀ c u d₁ d₂ : ℝ, 0 < c → 0 < d₁ →
      IsSlowlyIncreasingOn (centreCutSiegelSet ℚ c u d₁ d₂) (adelicHeight ℚ) h)
    (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hf : IsFactorizableTestFn ℚ f)
    {c u d₁ d₂ : ℝ} (hc : 0 < c) (hd₁ : 0 < d₁) (N : ℕ) :
    ∃ C : ℝ, ∀ x ∈ centreCutSiegelSet ℚ c u d₁ d₂, 1 ≤ adelicHeight ℚ x →
      ‖rightConv ℚ h f x‖ ≤ C * (adelicHeight ℚ x)⁻¹ ^ N := by
  obtain ⟨hfc, hfs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn ℚ f hf
  obtain ⟨C₀, hC₀c, h1C₀, hC₀⟩ := exists_isCompact_forall_inv_mul_unipotentGL2_mul_mem c u d₁ d₂ hc
  have hC₁ : IsCompact (C₀ * tsupport f) := hC₀c.mul hfs
  have hC₂ : IsCompact (C₀ * (C₀ * tsupport f)) := hC₀c.mul hC₁
  obtain ⟨B, M, hB⟩ := exists_norm_apply_mul_le h ξ hcont hleft hcentral hgrowth _ hC₂ c u d₁ d₂ hc hd₁
  obtain ⟨e₁, e₂, he₁, he₁₂, hslab⟩ := exists_detSlab_forall_mem hd₁ hfs
  obtain ⟨F, hF⟩ := exists_isFundamentalDomain_rationalUnipotent_restrict_detSlab he₁ he₁₂
  obtain ⟨D, hD⟩ := norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn ℚ f hf
    (c ^ (∑ w : InfinitePlace ℚ, w.mult)) u (N + M)
  have hC₁fin := adelicGLHaar_lt_top_of_isCompact hC₁
  refine ⟨|B| * |D| * (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ (C₀ * tsupport f)).toReal, fun x hx hxH => ?_⟩
  have hH0 : 0 < adelicHeight ℚ x := one_pos.trans_le hxH
  have hBH : 0 ≤ |B| * adelicHeight ℚ x ^ M := mul_nonneg (abs_nonneg B) (pow_nonneg hH0.le M)
  have hDH : 0 ≤ |D| * (adelicHeight ℚ x)⁻¹ ^ (N + M) :=
    mul_nonneg (abs_nonneg D) (pow_nonneg (inv_nonneg.mpr hH0.le) _)
  have harch : archHeight ℚ (glArch (𝓞 ℚ) ℚ x) = adelicHeight ℚ x := (adelicHeight_eq_archHeight_of_mem hx.1).symm
  have hxI : x ∈ integralWindowedSiegelSet ℚ (c ^ (∑ w : InfinitePlace ℚ, w.mult)) u :=
    centreCutSiegelSet_subset_integralWindowedSiegelSet hc.le hx

  have hKA : ∀ y : AdelicGL2 (𝓞 ℚ) ℚ,
      ‖(∑' β : ℚ, f (x⁻¹ * unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * y))
        - UnipotentAverage.unipotentAverage f x y‖ ≤ |D| * (adelicHeight ℚ x)⁻¹ ^ (N + M) := by
    intro y
    have hy := hD x hxI (by rw [harch]; exact hxH) y
    rw [harch] at hy
    exact hy.trans (mul_le_mul_of_nonneg_right (le_abs_self D) (pow_nonneg (inv_nonneg.mpr hH0.le) _))

  have hS : MeasurableSet (saturatedTranslate x (C₀ * tsupport f)) := measurableSet_saturatedTranslate x hC₁
  have hνS : ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂)).restrict F
      (saturatedTranslate x (C₀ * tsupport f)) ≤ adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ (C₀ * tsupport f) := by
    rw [Measure.restrict_apply hS, Set.inter_comm]
    exact measure_restrict_detSlab_inter_saturatedTranslate_le hF x _
  have hνS_lt := hνS.trans_lt hC₁fin

  have hh : ∀ y ∈ saturatedTranslate x (C₀ * (C₀ * tsupport f)), ‖h y‖ ≤ |B| * adelicHeight ℚ x ^ M := by
    intro y hy
    refine norm_le_of_mem_saturatedTranslate h (unipotentGL2_algebraMap_mul_invariant h hleft) (fun s hs => ?_) hy
    refine (hB x hx s hs).trans ?_
    rw [max_eq_right hxH]
    exact mul_le_mul_of_nonneg_right (le_abs_self B) (pow_nonneg hH0.le M)
  have hhS : ∀ y ∈ saturatedTranslate x (C₀ * tsupport f), ‖h y‖ ≤ |B| * adelicHeight ℚ x ^ M :=
    fun y hy => hh y (saturatedTranslate_mono x (subset_mul_left_of_one_mem h1C₀ _) hy)
  have hhn : ∀ t ∈ AdelicBox.adelicBox ℚ, ∀ y ∈ saturatedTranslate x (C₀ * tsupport f),
      ‖h (unipotentGL2 t * y)‖ ≤ |B| * adelicHeight ℚ x ^ M :=
    fun t ht y hy => hh _ (unipotentGL2_mul_mem_saturatedTranslate (hC₀ x hx t ht) hy)

  have hAinv : ∀ (β : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      UnipotentAverage.unipotentAverage f x (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * g)
        = UnipotentAverage.unipotentAverage f x g :=
    fun β g => UnipotentAverage.unipotentAverage_unipotentGL2_mul f x _ g
  have hAsupp : ∀ y, UnipotentAverage.unipotentAverage f x y ≠ 0 → y ∈ saturatedTranslate x (C₀ * tsupport f) := by
    intro y hy
    obtain ⟨t, ht⟩ := UnipotentAverage.exists_ne_zero_of_unipotentAverage_ne_zero hy
    exact mem_saturatedTranslate_mul_of_inv_mul_unipotentGL2_mul_mem (hC₀ x hx) (subset_tsupport f ht)
  obtain ⟨BA, hBA⟩ :=
    UnipotentAverage.exists_norm_unipotentAverage_le hfc hfs x _ (hC₁.image (continuous_const_mul x))
  have hAS : ∀ y ∈ saturatedTranslate x (C₀ * tsupport f), ‖UnipotentAverage.unipotentAverage f x y‖ ≤ BA :=
    fun y hy => norm_le_of_mem_saturatedTranslate _ hAinv (fun s hs => hBA _ ⟨s, hs, rfl⟩) hy
  have hAmeas : AEStronglyMeasurable (UnipotentAverage.unipotentAverage f x)
      (((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂)).restrict F) :=
    (UnipotentAverage.aestronglyMeasurable_unipotentAverage hfc x).restrict.restrict

  have hKsupp : ∀ y, (∑' β : ℚ, f (x⁻¹ * unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * y)) ≠ 0 →
      y ∈ saturatedTranslate x (C₀ * tsupport f) := fun y hy =>
    saturatedTranslate_mono x (subset_mul_left_of_one_mem h1C₀ _) (mem_saturatedTranslate_of_tsum_ne_zero f x y hy)

  have hunfold := rightConv_eq_setIntegral_mul_tsum h f hcont (fun β y => hleft _ y) hfc x
    (integrable_mul_comp_inv_mul hcont hfc hfs x) (fun z hz => hslab x hx z (subset_tsupport f hz)) hF
  have hzero := setIntegral_mul_eq_zero_of_isCuspidalFn h (fun β y => hleft _ y) hcusp
    (UnipotentAverage.unipotentAverage f x) (fun t y => UnipotentAverage.unipotentAverage_unipotentGL2_mul f x t y)
    hF (integrable_uncurry_mul_of_bounded hS hνS_lt.ne hcont hAmeas hAsupp hBH hhn hAS)
  rw [hunfold]
  by_cases hint : Integrable
    (fun y => h y * ∑' β : ℚ, f (x⁻¹ * unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * y))
    (((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂)).restrict F)
  swap
  · rw [integral_undef hint, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) ENNReal.toReal_nonneg)
      (pow_nonneg (inv_nonneg.mpr hH0.le) _)
  have hHA : Integrable (fun y => h y * UnipotentAverage.unipotentAverage f x y)
      (((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂)).restrict F) :=
    integrable_of_support_subset_of_bounded hS hνS_lt.ne (hcont.aestronglyMeasurable.mul hAmeas)
      (fun y hy => hAsupp y (right_ne_zero_of_mul hy))
      (fun y hy => by rw [norm_mul]; exact mul_le_mul (hhS y hy) (hAS y hy) (norm_nonneg _) hBH)
  have hsub := integral_sub hint hHA
  rw [hzero, sub_zero] at hsub
  rw [← hsub]
  have hvanish : ∀ y ∉ saturatedTranslate x (C₀ * tsupport f),
      h y * (∑' β : ℚ, f (x⁻¹ * unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * y))
        - h y * UnipotentAverage.unipotentAverage f x y = 0 := by
    intro y hy
    have hK0 : (∑' β : ℚ, f (x⁻¹ * unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * y)) = 0 := by
      by_contra hne
      exact hy (hKsupp y hne)
    have hA0 : UnipotentAverage.unipotentAverage f x y = 0 := by
      by_contra hne
      exact hy (hAsupp y hne)
    rw [hK0, hA0, mul_zero, sub_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvanish]
  refine (norm_setIntegral_le_of_norm_le_const
    (C := |B| * adelicHeight ℚ x ^ M * (|D| * (adelicHeight ℚ x)⁻¹ ^ (N + M))) hνS_lt fun y hy => ?_).trans ?_
  · rw [← mul_sub, norm_mul]
    exact mul_le_mul (hhS y hy) (hKA y) (norm_nonneg _) hBH
  have hreal : (((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂)).restrict F).real
      (saturatedTranslate x (C₀ * tsupport f)) ≤ (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ (C₀ * tsupport f)).toReal :=
    ENNReal.toReal_mono hC₁fin.ne hνS
  have hpow : adelicHeight ℚ x ^ M * (adelicHeight ℚ x)⁻¹ ^ (N + M) = (adelicHeight ℚ x)⁻¹ ^ N := by
    rw [pow_add, mul_comm ((adelicHeight ℚ x)⁻¹ ^ N), ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hH0.ne', one_pow,
      one_mul]
  calc |B| * adelicHeight ℚ x ^ M * (|D| * (adelicHeight ℚ x)⁻¹ ^ (N + M))
        * (((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (detSlab e₁ e₂)).restrict F).real
            (saturatedTranslate x (C₀ * tsupport f))
      ≤ |B| * adelicHeight ℚ x ^ M * (|D| * (adelicHeight ℚ x)⁻¹ ^ (N + M))
          * (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ (C₀ * tsupport f)).toReal :=
        mul_le_mul_of_nonneg_left hreal (mul_nonneg hBH hDH)
    _ = |B| * |D| * (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ (C₀ * tsupport f)).toReal
          * (adelicHeight ℚ x ^ M * (adelicHeight ℚ x)⁻¹ ^ (N + M)) := by ring
    _ = |B| * |D| * (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ (C₀ * tsupport f)).toReal * (adelicHeight ℚ x)⁻¹ ^ N := by
        rw [hpow]

end HighPart
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

section HeadsOfRecord

private theorem exists_forall_norm_rightConv_le_of_adelicHeight_le_one
    (h : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hcont : Continuous h)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      h (globalPoints (𝓞 ℚ) ℚ γ * g) = h g)
    (hcentral : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      h (centralScalar (𝓞 ℚ) ℚ z * g) = ((ξ z : ℂˣ) : ℂ) * h g)
    (hgrowth : ∀ c u d₁ d₂ : ℝ, 0 < c → 0 < d₁ →
      IsSlowlyIncreasingOn (centreCutSiegelSet ℚ c u d₁ d₂) (adelicHeight ℚ) h)
    {f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hfc : Continuous f) (hfs : HasCompactSupport f)
    {c u d₁ d₂ : ℝ} (hc : 0 < c) (hd₁ : 0 < d₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ centreCutSiegelSet ℚ c u d₁ d₂, adelicHeight ℚ x ≤ 1 → ‖rightConv ℚ h f x‖ ≤ C := by
  haveI : (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
  obtain ⟨B, M, hB⟩ := exists_norm_apply_mul_le h ξ hcont hleft hcentral hgrowth _ hfs c u d₁ d₂ hc hd₁
  have hfint : Integrable f (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := hfc.integrable_of_hasCompactSupport hfs
  refine ⟨|B| * ∫ k, ‖f k‖ ∂(adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ),
    mul_nonneg (abs_nonneg B) (integral_nonneg fun k => norm_nonneg _), fun x hx hxH => ?_⟩
  rw [rightConv_apply]
  show ‖∫ k, h (x * k) * f k ∂(adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ)‖ ≤ _
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hfint.norm.const_mul |B|) (Filter.Eventually.of_forall fun k => ?_)
  rw [norm_mul]
  by_cases hk : f k = 0
  · rw [hk, norm_zero, mul_zero, mul_zero]
  · refine mul_le_mul_of_nonneg_right ((hB x hx k (subset_tsupport f hk)).trans ?_) (norm_nonneg _)
    rw [max_eq_left hxH, one_pow, mul_one]
    exact le_abs_self B

private theorem isRapidlyDecreasingOn_rightConv
    (h : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hcont : Continuous h)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      h (globalPoints (𝓞 ℚ) ℚ γ * g) = h g)
    (hcentral : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      h (centralScalar (𝓞 ℚ) ℚ z * g) = ((ξ z : ℂˣ) : ℂ) * h g)
    (hcusp : @IsCuspidalFn _ (adeleBorel (𝓞 ℚ) ℚ) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 ℚ) ℚ) (adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
      unipotentGL2 h)
    (hgrowth : ∀ c u d₁ d₂ : ℝ, 0 < c → 0 < d₁ →
      IsSlowlyIncreasingOn (centreCutSiegelSet ℚ c u d₁ d₂) (NumberField.AdelicHeight.adelicHeight ℚ) h)
    (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hf : IsFactorizableTestFn ℚ f)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (hd₁ : 0 < d₁) :
    IsRapidlyDecreasingOn (centreCutSiegelSet ℚ c u d₁ d₂) (NumberField.AdelicHeight.adelicHeight ℚ)
      (rightConv ℚ h f) := by
  intro N
  obtain ⟨hfc, hfs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn ℚ f hf
  obtain ⟨C₁, hC₁, hlow⟩ :=
    exists_forall_norm_rightConv_le_of_adelicHeight_le_one h ξ hcont hleft hcentral hgrowth hfc hfs (u := u) (d₂ := d₂)
      hc hd₁
  obtain ⟨C₂, hhigh⟩ :=
    exists_forall_norm_rightConv_le_of_one_le_adelicHeight h ξ hcont hleft hcentral hcusp hgrowth f hf (u := u)
      (d₂ := d₂) hc hd₁ N
  refine ⟨max C₁ C₂, fun x hx => ?_⟩
  have hH0 : 0 < adelicHeight ℚ x := adelicHeight_pos x
  rcases le_total (adelicHeight ℚ x) 1 with hle | hge
  · have h1 : (1 : ℝ) ≤ (adelicHeight ℚ x)⁻¹ ^ N := one_le_pow₀ ((one_le_inv₀ hH0).mpr hle)
    calc ‖rightConv ℚ h f x‖ ≤ C₁ := hlow x hx hle
      _ = C₁ * 1 := (mul_one C₁).symm
      _ ≤ max C₁ C₂ * (adelicHeight ℚ x)⁻¹ ^ N :=
        mul_le_mul (le_max_left C₁ C₂) h1 zero_le_one (le_max_of_le_left hC₁)
  · exact (hhigh x hx hge).trans
      (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (pow_nonneg (inv_nonneg.mpr hH0.le) N))

private theorem memLp_two_rightConv_restrict
    (h : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hcont : Continuous h)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      h (globalPoints (𝓞 ℚ) ℚ γ * g) = h g)
    (hcentral : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      h (centralScalar (𝓞 ℚ) ℚ z * g) = ((ξ z : ℂˣ) : ℂ) * h g)
    (hcusp : @IsCuspidalFn _ (adeleBorel (𝓞 ℚ) ℚ) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 ℚ) ℚ) (adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
      unipotentGL2 h)
    (hgrowth : ∀ c u d₁ d₂ : ℝ, 0 < c → 0 < d₁ →
      IsSlowlyIncreasingOn (centreCutSiegelSet ℚ c u d₁ d₂) (NumberField.AdelicHeight.adelicHeight ℚ) h)
    (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hf : IsFactorizableTestFn ℚ f)
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hc : 0 < c) (hd₁ : 0 < d₁) :
    MemLp (rightConv ℚ h f) 2
      ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)) := by
  have hbound : ∀ t : AdelicGL2 (𝓞 ℚ) ℚ, ∃ Bt : ℝ,
      ∀ s ∈ centreCutSiegelSet ℚ c u d₁ d₂, ‖rightConv ℚ h f (s * t)‖ ≤ Bt := by
    intro t
    obtain ⟨Bt, hBt⟩ := isRapidlyDecreasingOn_rightConv h ξ hcont hleft hcentral hcusp hgrowth _
      (isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn ℚ f hf t) c u d₁ d₂ hc hd₁ 0
    refine ⟨Bt, fun s hs => ?_⟩
    rw [rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply ℚ h f s t]
    have hs' := hBt s hs
    rwa [pow_zero, mul_one] at hs'
  choose Bf hBf using hbound
  exact memLp_two_restrict_iUnion_image_mul_right (rightConv ℚ h f)
    (continuous_rightConv_and_contDiff_of_isFactorizableTestFn ℚ h hcont f hf).1 hc u hd₁ d₂ T Bf
    fun t _ s hs => hBf t s hs

end HeadsOfRecord
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end AutomorphicForm.GodementEstimate
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end GodementAssembly
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

section CosetSystemLevel

set_option autoImplicit false

p2m_open "NumberField IsDedekindDomain AutomorphicForm~continuous_unipotentGL2 P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm LocalGL2 AdelicDock NumberField.AdelicLevel"
open HeckeIntegralSeam HeckePair

namespace CosetSystemLevel

section Generic

variable {G : Type*} [Group G] {ι ι' : Type*}

private theorem mem_doubleCoset_of_le {U V : Subgroup G} (hUV : U ≤ V) {g x : G} (hx : x ∈ doubleCoset U g) :
    x ∈ doubleCoset V g := by
  obtain ⟨u, hu, w, hw, rfl⟩ := mem_doubleCoset_iff.mp hx
  exact mem_doubleCoset_iff.mpr ⟨u, hUV hu, w, hUV hw, rfl⟩

private theorem mem_of_mem_doubleCoset {U L : Subgroup G} (hUL : U ≤ L) {g : G} (hg : g ∈ L) {x : G}
    (hx : x ∈ doubleCoset U g) : x ∈ L := by
  obtain ⟨u, hu, w, hw, rfl⟩ := mem_doubleCoset_iff.mp hx
  exact L.mul_mem (L.mul_mem (hUL hu) hg) (hUL hw)

private theorem mul_mul_mul_eq_of_comm {u₁ c₁ g u₂ c₂ : G} (h1 : c₁ * g = g * c₁) (h2 : c₁ * u₂ = u₂ * c₁) :
    u₁ * c₁ * g * (u₂ * c₂) = u₁ * g * u₂ * (c₁ * c₂) := by
  calc u₁ * c₁ * g * (u₂ * c₂) = u₁ * (c₁ * g) * u₂ * c₂ := by group
    _ = u₁ * g * (c₁ * u₂) * c₂ := by rw [h1]; group
    _ = u₁ * g * u₂ * (c₁ * c₂) := by rw [h2]; group

private theorem isHeckeCosetSystem_of_decomp (U V C L : Subgroup G) (g : G) (reps : ι → G)
    (hsys : IsHeckeCosetSystem U g reps) (hUV : U ≤ V) (hCV : C ≤ V)
    (hdecomp : ∀ x ∈ V, ∃ u ∈ U, ∃ c ∈ C, x = u * c)
    (hCg : ∀ c ∈ C, c * g = g * c) (hCU : ∀ c ∈ C, ∀ u ∈ U, c * u = u * c)
    (hUL : U ≤ L) (hgL : g ∈ L) (hVL : ∀ x ∈ V, x ∈ L → x ∈ U) :
    IsHeckeCosetSystem V g reps where
  mem_doubleCoset i := mem_doubleCoset_of_le hUV (hsys.mem_doubleCoset i)
  covers x hx := by
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := mem_doubleCoset_iff.mp hx
    obtain ⟨u₁, hu₁, c₁, hc₁, rfl⟩ := hdecomp v₁ hv₁
    obtain ⟨u₂, hu₂, c₂, hc₂, rfl⟩ := hdecomp v₂ hv₂
    have hy : u₁ * g * u₂ ∈ doubleCoset U g := mem_doubleCoset_iff.mpr ⟨u₁, hu₁, u₂, hu₂, rfl⟩
    obtain ⟨i, hi⟩ := hsys.covers _ hy
    refine ⟨i, ?_⟩
    have hU : (u₁ * g * u₂)⁻¹ * reps i ∈ U := QuotientGroup.eq.mp hi
    rw [mul_mul_mul_eq_of_comm (hCg c₁ hc₁) (hCU c₁ hc₁ u₂ hu₂), QuotientGroup.eq]
    have hmem : (u₁ * g * u₂ * (c₁ * c₂))⁻¹ * reps i = (c₁ * c₂)⁻¹ * ((u₁ * g * u₂)⁻¹ * reps i) := by
      group
    rw [hmem]
    exact V.mul_mem (V.inv_mem (hCV (C.mul_mem hc₁ hc₂))) (hUV hU)
  mk_injective := by
    intro i j hij
    have hV : (reps i)⁻¹ * reps j ∈ V := QuotientGroup.eq.mp hij
    have hLi : reps i ∈ L := mem_of_mem_doubleCoset hUL hgL (hsys.mem_doubleCoset i)
    have hLj : reps j ∈ L := mem_of_mem_doubleCoset hUL hgL (hsys.mem_doubleCoset j)
    exact hsys.mk_injective (QuotientGroup.eq.mpr (hVL _ hV (L.mul_mem (L.inv_mem hLi) hLj)))

private theorem isHeckeCosetSystem_restrict (U V C L : Subgroup G) (g : G) (reps : ι → G)
    (hsys : IsHeckeCosetSystem V g reps) (hreps : ∀ i, reps i ∈ L) (hUV : U ≤ V)
    (hdecomp : ∀ x ∈ V, ∃ u ∈ U, ∃ c ∈ C, x = u * c)
    (hCg : ∀ c ∈ C, c * g = g * c) (hCU : ∀ c ∈ C, ∀ u ∈ U, c * u = u * c)
    (hUL : U ≤ L) (hgL : g ∈ L) (hVL : ∀ x ∈ V, x ∈ L → x ∈ U) (hCL : ∀ c ∈ C, c ∈ L → c = 1) :
    IsHeckeCosetSystem U g reps where
  mem_doubleCoset i := by
    obtain ⟨v₁, hv₁, v₂, hv₂, hx⟩ := mem_doubleCoset_iff.mp (hsys.mem_doubleCoset i)
    obtain ⟨u₁, hu₁, c₁, hc₁, rfl⟩ := hdecomp v₁ hv₁
    obtain ⟨u₂, hu₂, c₂, hc₂, rfl⟩ := hdecomp v₂ hv₂
    rw [mul_mul_mul_eq_of_comm (hCg c₁ hc₁) (hCU c₁ hc₁ u₂ hu₂)] at hx
    have hyL : u₁ * g * u₂ ∈ L := L.mul_mem (L.mul_mem (hUL hu₁) hgL) (hUL hu₂)
    have hcL : c₁ * c₂ ∈ L := by
      have : c₁ * c₂ = (u₁ * g * u₂)⁻¹ * reps i := by rw [← hx]; group
      rw [this]
      exact L.mul_mem (L.inv_mem hyL) (hreps i)
    have hc1 : c₁ * c₂ = 1 := hCL _ (C.mul_mem hc₁ hc₂) hcL
    rw [hc1, mul_one] at hx
    exact mem_doubleCoset_iff.mpr ⟨u₁, hu₁, u₂, hu₂, hx⟩
  covers x hx := by
    obtain ⟨i, hi⟩ := hsys.covers x (mem_doubleCoset_of_le hUV hx)
    refine ⟨i, QuotientGroup.eq.mpr (hVL _ (QuotientGroup.eq.mp hi) ?_)⟩
    exact L.mul_mem (L.inv_mem (mem_of_mem_doubleCoset hUL hgL hx)) (hreps i)
  mk_injective := by
    intro i j hij
    exact hsys.mk_injective (QuotientGroup.eq.mpr (hUV (QuotientGroup.eq.mp hij)))

private theorem isHeckeCosetSystem_comp_equiv {U : Subgroup G} {g : G} {reps : ι → G}
    (hsys : IsHeckeCosetSystem U g reps) (e : ι' ≃ ι) : IsHeckeCosetSystem U g (reps ∘ e) where
  mem_doubleCoset i := hsys.mem_doubleCoset (e i)
  covers x hx := by
    obtain ⟨i, hi⟩ := hsys.covers x hx
    exact ⟨e.symm i, by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hi⟩
  mk_injective := by
    intro i j hij
    exact e.injective (hsys.mk_injective hij)

end Generic
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

section Adelic

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private noncomputable def embedAt : GL (Fin 2) (v.adicCompletion F) →* AdelicGL2 (𝓞 F) F :=
  (finEmbed (𝓞 F) F).comp (localEmbed (𝓞 F) F v)

private noncomputable def componentAt : AdelicGL2 (𝓞 F) F →* GL (Fin 2) (v.adicCompletion F) :=
  (finComponent (𝓞 F) F v).comp (glFin (𝓞 F) F)

private theorem componentAt_embedAt (k : GL (Fin 2) (v.adicCompletion F)) : componentAt F v (embedAt F v k) = k := by
  simp only [componentAt, embedAt, MonoidHom.comp_apply]
  rw [glFin_finEmbed, finComponent_localEmbed_self]

private noncomputable def integralImage : Subgroup (AdelicGL2 (𝓞 F) F) :=
  (integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F)).map (embedAt F v)

private noncomputable def localImage : Subgroup (AdelicGL2 (𝓞 F) F) := (embedAt F v).range

private noncomputable def levelGroup (N : Ideal (𝓞 F)) : Subgroup (AdelicGL2 (𝓞 F) F) :=
  levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F

private noncomputable def awayPart (N : Ideal (𝓞 F)) : Subgroup (AdelicGL2 (𝓞 F) F) :=
  levelGroup F N ⊓ (componentAt F v).ker

private theorem ext_of_components {x y : AdelicGL2 (𝓞 F) F} (harch : glArch (𝓞 F) F x = glArch (𝓞 F) F y)
    (hfin : ∀ w : HeightOneSpectrum (𝓞 F),
      finComponent (𝓞 F) F w (glFin (𝓞 F) F x) = finComponent (𝓞 F) F w (glFin (𝓞 F) F y)) :
    x = y := by
  apply Units.ext
  ext i j
  apply Prod.ext
  · have h := congrArg (fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
      (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) harch
    simpa only [glArch_apply] using h
  · ext w : 1
    have h := congrArg (fun g : GL (Fin 2) (w.adicCompletion F) =>
      (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) i j) (hfin w)
    first | exact h | simpa only [finComponent_apply, glFin_apply] using h | simpa +zetaDelta only [finComponent_apply, glFin_apply] using h

private theorem commute_embedAt {c : AdelicGL2 (𝓞 F) F} (hc : c ∈ finiteAdelicGL2Subgroup F)
    (hcv : componentAt F v c = 1) (k : GL (Fin 2) (v.adicCompletion F)) :
    c * embedAt F v k = embedAt F v k * c := by
  have harch_c : glArch (𝓞 F) F c = 1 := (mem_finiteAdelicGL2Subgroup_iff F c).mp hc
  have harch_e : glArch (𝓞 F) F (embedAt F v k) = 1 := glArch_finEmbed (𝓞 F) F _
  have he : glFin (𝓞 F) F (embedAt F v k) = localEmbed (𝓞 F) F v k := glFin_finEmbed (𝓞 F) F _
  have hcv' : finComponent (𝓞 F) F v (glFin (𝓞 F) F c) = 1 := hcv
  apply ext_of_components F
  · rw [map_mul, map_mul, harch_c, harch_e]
  · intro w
    simp only [map_mul, he]
    by_cases hw : w = v
    · subst hw
      rw [hcv', finComponent_localEmbed_self, one_mul, mul_one]
    · rw [finComponent_localEmbed_of_ne (𝓞 F) F v k hw, one_mul, mul_one]

private theorem eq_one_of_mem_localImage_of_componentAt_eq_one {c : AdelicGL2 (𝓞 F) F} (hc : c ∈ localImage F v)
    (hcv : componentAt F v c = 1) : c = 1 := by
  obtain ⟨k, rfl⟩ := hc
  have hk : k = 1 := by rw [← componentAt_embedAt F v k]; exact hcv
  rw [hk, map_one]

private theorem algebraMap_integers_apply (x : v.adicCompletionIntegers F) :
    algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) x = (x : v.adicCompletion F) :=
  rfl

private theorem mem_integralSubgroup_of_entries (k : GL (Fin 2) (v.adicCompletion F))
    (h : ∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F)
    (h' : ∀ i j, ((k⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈
      v.adicCompletionIntegers F) :
    k ∈ integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F) := by
  set A : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers F) :=
    Matrix.of fun i j => ⟨(k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j, h i j⟩ with hA
  set B : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers F) :=
    Matrix.of fun i j =>
      ⟨((k⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j, h' i j⟩
    with hB
  have hinj : Function.Injective
      ((algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)).mapMatrix (m := Fin 2)) := by
    intro M N hMN
    ext i j : 2
    have := congrFun (congrFun (congrArg (fun P => (P : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) hMN) i) j
    exact this
  have hAmap : (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)).mapMatrix A =
      (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) := by
    ext i j; rfl
  have hBmap : (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)).mapMatrix B =
      ((k⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) := by
    ext i j; rfl
  have hAB : A * B = 1 := by
    apply hinj
    rw [map_mul, hAmap, hBmap, map_one]
    exact Units.mul_inv k
  have hBA : B * A = 1 := by
    apply hinj
    rw [map_mul, hAmap, hBmap, map_one]
    exact Units.inv_mul k
  refine mem_integralSubgroup_iff.mpr ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  apply Units.ext
  exact hAmap

private theorem componentAt_mem_integralSubgroup_of_mem_levelOne {N : Ideal (𝓞 F)} {x : AdelicGL2 (𝓞 F) F}
    (hx : x ∈ levelOne (𝓞 F) F N) :
    componentAt F v x ∈ integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F) := by
  have hx' : glFin (𝓞 F) F x ∈ finiteLevelOne (𝓞 F) F N := hx
  refine mem_integralSubgroup_of_entries F v _ (fun i j => ?_) (fun i j => ?_)
  · simp only [componentAt, MonoidHom.comp_apply, finComponent_apply]
    exact hx'.1.integral i j v
  · have hinv : ((componentAt F v x)⁻¹ : GL (Fin 2) (v.adicCompletion F)) =
        finComponent (𝓞 F) F v ((glFin (𝓞 F) F x)⁻¹) := by
      simp only [componentAt, MonoidHom.comp_apply, map_inv]
    rw [hinv, finComponent_apply]
    exact hx'.2.integral i j v

private theorem mem_integralImage_of_mem_levelGroup_of_mem_localImage {N : Ideal (𝓞 F)} {x : AdelicGL2 (𝓞 F) F}
    (hxV : x ∈ levelGroup F N) (hxL : x ∈ localImage F v) : x ∈ integralImage F v := by
  obtain ⟨k, rfl⟩ := hxL
  refine ⟨k, ?_, rfl⟩
  have hk := componentAt_mem_integralSubgroup_of_mem_levelOne F v hxV.1
  rwa [componentAt_embedAt] at hk

private theorem integralImage_le_localImage : integralImage F v ≤ localImage F v := by
  rintro _ ⟨k, -, rfl⟩
  exact ⟨k, rfl⟩

private theorem integralImage_le_levelGroup {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N) :
    integralImage F v ≤ levelGroup F N := by
  rintro _ ⟨k, hk, rfl⟩
  exact finEmbed_localEmbed_mem_levelOne_inf_finiteAdelicGL2Subgroup F v hv hk

private theorem exists_decomp_of_mem_levelGroup {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N) {x : AdelicGL2 (𝓞 F) F}
    (hx : x ∈ levelGroup F N) :
    ∃ u ∈ integralImage F v, ∃ c ∈ awayPart F v N, x = u * c := by
  have huU : embedAt F v (componentAt F v x) ∈ integralImage F v :=
    ⟨_, componentAt_mem_integralSubgroup_of_mem_levelOne F v hx.1, rfl⟩
  have huV : embedAt F v (componentAt F v x) ∈ levelGroup F N := integralImage_le_levelGroup F v hv huU
  refine ⟨embedAt F v (componentAt F v x), huU, (embedAt F v (componentAt F v x))⁻¹ * x,
    ⟨(levelGroup F N).mul_mem ((levelGroup F N).inv_mem huV) hx, ?_⟩, by group⟩
  show componentAt F v ((embedAt F v (componentAt F v x))⁻¹ * x) = 1
  rw [map_mul, map_inv, componentAt_embedAt, inv_mul_cancel]

private
theorem awayPart_commute {N : Ideal (𝓞 F)} {c : AdelicGL2 (𝓞 F) F} (hc : c ∈ awayPart F v N) {y : AdelicGL2 (𝓞 F) F}
    (hy : y ∈ localImage F v) : c * y = y * c := by
  obtain ⟨k, rfl⟩ := hy
  exact commute_embedAt F v hc.1.2 hc.2 k

private theorem isHeckeCosetSystem_levelGroup {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N) {g : AdelicGL2 (𝓞 F) F}
    (hg : g ∈ localImage F v) {ι : Type*} {reps : ι → AdelicGL2 (𝓞 F) F}
    (hsys : IsHeckeCosetSystem (integralImage F v) g reps) :
    IsHeckeCosetSystem (levelGroup F N) g reps :=
  isHeckeCosetSystem_of_decomp (integralImage F v) (levelGroup F N) (awayPart F v N) (localImage F v) g reps
    hsys (integralImage_le_levelGroup F v hv) inf_le_left (fun _x hx => exists_decomp_of_mem_levelGroup F v hv hx)
    (fun _c hc => awayPart_commute F v hc hg)
    (fun _c hc _u hu => awayPart_commute F v hc (integralImage_le_localImage F v hu))
    (integralImage_le_localImage F v) hg
    (fun _x hxV hxL => mem_integralImage_of_mem_levelGroup_of_mem_localImage F v hxV hxL)

private theorem isHeckeCosetSystem_integralImage {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N) {g : AdelicGL2 (𝓞 F) F}
    (hg : g ∈ localImage F v) {ι : Type*} {reps : ι → AdelicGL2 (𝓞 F) F}
    (hsys : IsHeckeCosetSystem (levelGroup F N) g reps) (hreps : ∀ i, reps i ∈ localImage F v) :
    IsHeckeCosetSystem (integralImage F v) g reps :=
  isHeckeCosetSystem_restrict (integralImage F v) (levelGroup F N) (awayPart F v N) (localImage F v) g reps
    hsys hreps (integralImage_le_levelGroup F v hv) (fun _x hx => exists_decomp_of_mem_levelGroup F v hv hx)
    (fun _c hc => awayPart_commute F v hc hg)
    (fun _c hc _u hu => awayPart_commute F v hc (integralImage_le_localImage F v hu))
    (integralImage_le_localImage F v) hg
    (fun _x hxV hxL => mem_integralImage_of_mem_levelGroup_of_mem_localImage F v hxV hxL)
    (fun _c hc hcL => eq_one_of_mem_localImage_of_componentAt_eq_one F v hcL hc.2)

private theorem exists_isHeckeCosetSystem_integralImage_heckeGen :
    heckeGen (𝓞 F) F v ∈ localImage F v ∧
      ∃ reps : Option (𝓞 F ⧸ v.asIdeal) → AdelicGL2 (𝓞 F) F,
        IsHeckeCosetSystem (integralImage F v) (heckeGen (𝓞 F) F v) reps ∧
          ∀ i, reps i ∈ localImage F v := by
  obtain ⟨ϖ, hϖ0, -, hgen, sec, -, hsys⟩ := exists_isHeckeCosetSystem_localRep_heckeGen F v
  have hg : heckeGen (𝓞 F) F v ∈ localImage F v := ⟨_, hgen⟩
  have htop : ¬ v.asIdeal ∣ (⊤ : Ideal (𝓞 F)) := fun h =>
    v.isPrime.ne_top (top_le_iff.mp (Ideal.dvd_iff_le.mp h))
  have hsysU := isHeckeCosetSystem_integralImage F v htop hg (hsys ⊤ htop) (fun i => ⟨_, rfl⟩)
  exact ⟨hg, _, hsysU, fun i => ⟨_, rfl⟩⟩

private theorem card_quotient_eq_absNorm [Fintype (𝓞 F ⧸ v.asIdeal)] :
    Fintype.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
  rw [← Nat.card_eq_fintype_card, Ideal.absNorm_apply, Submodule.cardQuot_apply]

private noncomputable def finEquivOption [Fintype (𝓞 F ⧸ v.asIdeal)] :
    Fin (Ideal.absNorm v.asIdeal + 1) ≃ Option (𝓞 F ⧸ v.asIdeal) :=
  Fintype.equivOfCardEq (by rw [Fintype.card_fin, Fintype.card_option, card_quotient_eq_absNorm])

private theorem isHeckeCosetEigenfunctionAt_integralImage [Fintype (𝓞 F ⧸ v.asIdeal)] {N : Ideal (𝓞 F)}
    (hv : ¬ v.asIdeal ∣ N) (hg : heckeGen (𝓞 F) F v ∈ localImage F v)
    {reps : Option (𝓞 F ⧸ v.asIdeal) → AdelicGL2 (𝓞 F) F}
    (hsys : IsHeckeCosetSystem (levelGroup F N) (heckeGen (𝓞 F) F v) reps) (hreps : ∀ i, reps i ∈ localImage F v)
    {h : AdelicGL2 (𝓞 F) F → ℂ} {c : ℂ}
    (hsum : ∀ g : AdelicGL2 (𝓞 F) F, (∑ x, h (g * reps (some x))) + h (g * reps none) = c * h g) :
    SmoothCusp.IsHeckeCosetEigenfunctionAt F (integralImage F v) (heckeGen (𝓞 F) F v) v h c := by
  refine ⟨reps ∘ finEquivOption F v,
    isHeckeCosetSystem_comp_equiv (isHeckeCosetSystem_integralImage F v hv hg hsys hreps) _, fun g => ?_⟩
  calc SmoothCusp.heckeCosetSum F (reps ∘ finEquivOption F v) h g
      = ∑ i, h (g * reps (finEquivOption F v i)) := rfl
    _ = ∑ i, h (g * reps i) := Equiv.sum_comp (finEquivOption F v) (fun i => h (g * reps i))
    _ = h (g * reps none) + ∑ x, h (g * reps (some x)) := Fintype.sum_option _
    _ = c * h g := by rw [add_comm]; exact hsum g

private theorem algebraMap_eq_uniformizerUnit_of_embedAt_diagPi_eq {ϖ : v.adicCompletionIntegers F}
    (hϖ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0)
    (hgen : embedAt F v (diagPi ϖ hϖ0) = heckeGen (𝓞 F) F v) :
    algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ = (uniformizerUnit F v : v.adicCompletion F) := by
  have h00 := congrArg (fun x : AdelicGL2 (𝓞 F) F =>
    (componentAt F v x : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0) hgen
  simp only [componentAt_embedAt] at h00
  have hL : (diagPi ϖ hϖ0 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0
      = algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ := rfl
  rw [hL] at h00
  rw [h00]
  show (finComponent (𝓞 F) F v (glFin (𝓞 F) F (heckeGenAt (𝓞 F) F v (uniformizerUnit F v))) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0 = _
  rw [finComponent_apply, glFin_apply]
  show ((finIncl (𝓞 F) F (localUnit (𝓞 F) F v (uniformizerUnit F v) : FiniteAdeleRing (𝓞 F) F)).2) v = _
  rw [finIncl_apply_snd]
  exact localUnit_apply_self (𝓞 F) F v _

end Adelic
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end CosetSystemLevel
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end CosetSystemLevel
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

section HeckeThroughConv

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel
p2m_open "AutomorphicForm~continuous_unipotentGL2 P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm AutomorphicForm.SmoothCusp IsDedekindDomain UnramifiedWhittaker HeckeIntegralSeam"

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace HeckeThroughConv

variable (v : HeightOneSpectrum (𝓞 ℚ))

private abbrev sphericalImage : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ) :=
  (LocalGL2.integralSubgroup (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)).map
    ((AdelicDock.finEmbed (𝓞 ℚ) ℚ).comp (AdelicDock.localEmbed (𝓞 ℚ) ℚ v))

private theorem sphericalImage_le_localImage : sphericalImage v ≤ CosetSystemLevel.localImage ℚ v := by
  rintro x ⟨k, -, rfl⟩
  exact MonoidHom.mem_range.mpr ⟨k, rfl⟩

private theorem placeEmbed_map_mem (kv : GL (Fin 2) (v.adicCompletionIntegers ℚ)) :
    placeEmbed ℚ v (Matrix.GeneralLinearGroup.map
      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) kv) ∈ sphericalImage v :=
  Subgroup.mem_map.mpr ⟨_, ⟨kv, rfl⟩, rfl⟩

private theorem exists_eq_placeEmbed_of_mem_doubleCoset {x : AdelicGL2 (𝓞 ℚ) ℚ}
    (hx : x ∈ HeckePair.doubleCoset (sphericalImage v) (heckeGen (𝓞 ℚ) ℚ v)) :
    ∃ m : GL (Fin 2) (v.adicCompletion ℚ), x = placeEmbed ℚ v m := by
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := (HeckePair.mem_doubleCoset_iff (U := sphericalImage v)).mp hx
  have hg : heckeGen (𝓞 ℚ) ℚ v ∈ CosetSystemLevel.localImage ℚ v :=
    (CosetSystemLevel.exists_isHeckeCosetSystem_integralImage_heckeGen ℚ v).1
  have h₁ : u₁ ∈ CosetSystemLevel.localImage ℚ v := sphericalImage_le_localImage v hu₁
  have h₂ : u₂ ∈ CosetSystemLevel.localImage ℚ v := sphericalImage_le_localImage v hu₂
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ hg) h₂)
  exact ⟨m, hm.symm⟩

private theorem isHeckeCosetEigenfunctionAt_rightConv (h f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (a : ℂ)
    (hsph : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ∀ k ∈ sphericalImage v, h (g * k) = h g)
    (hhecke : IsHeckeCosetEigenfunctionAt ℚ (sphericalImage v) (heckeGen (𝓞 ℚ) ℚ v) v h a)
    (hsupp : ∀ z : AdelicGL2 (𝓞 ℚ) ℚ, f z ≠ 0 → ∃ z₁ z₂ : AdelicGL2 (𝓞 ℚ) ℚ,
      z = z₁ * z₂ ∧ z₂ ∈ sphericalImage v ∧
        ∀ xv : GL (Fin 2) (v.adicCompletion ℚ), z₁ * placeEmbed ℚ v xv = placeEmbed ℚ v xv * z₁)
    (hint : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      Integrable (fun z => h (g * z) * f z) (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ)) :
    IsHeckeCosetEigenfunctionAt ℚ (sphericalImage v) (heckeGen (𝓞 ℚ) ℚ v) v (rightConv ℚ h f) a := by
  obtain ⟨reps, hsys, hsum⟩ := hhecke
  have hpure : ∀ j, ∃ m : GL (Fin 2) (v.adicCompletion ℚ), reps j = placeEmbed ℚ v m := fun j =>
    exists_eq_placeEmbed_of_mem_doubleCoset v (hsys.mem_doubleCoset j)
  have H := AutomorphicForm.heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps ℚ v
    (sphericalImage v) (placeEmbed_map_mem v) reps hsys hpure h hsph a ⟨reps, hsys, hsum⟩ f hsupp
    hint (fun _ : Fin 1 => (1 : AdelicGL2 (𝓞 ℚ) ℚ)) (fun _ => (1 : ℂ))
    (fun _ xv => by simp)
  obtain ⟨-, -, H₃⟩ := H
  simpa only [Fin.sum_univ_one, one_mul, mul_one] using H₃

private theorem rightConv_mul_placeEmbed_map (h f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (a : ℂ)
    (hsph : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ∀ k ∈ sphericalImage v, h (g * k) = h g)
    (hhecke : IsHeckeCosetEigenfunctionAt ℚ (sphericalImage v) (heckeGen (𝓞 ℚ) ℚ v) v h a)
    (hsupp : ∀ z : AdelicGL2 (𝓞 ℚ) ℚ, f z ≠ 0 → ∃ z₁ z₂ : AdelicGL2 (𝓞 ℚ) ℚ,
      z = z₁ * z₂ ∧ z₂ ∈ sphericalImage v ∧
        ∀ xv : GL (Fin 2) (v.adicCompletion ℚ), z₁ * placeEmbed ℚ v xv = placeEmbed ℚ v xv * z₁)
    (hint : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      Integrable (fun z => h (g * z) * f z) (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
    (kv : GL (Fin 2) (v.adicCompletionIntegers ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    rightConv ℚ h f (g * placeEmbed ℚ v (Matrix.GeneralLinearGroup.map
      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) kv)) = rightConv ℚ h f g := by
  obtain ⟨reps, hsys, hsum⟩ := hhecke
  have hpure : ∀ j, ∃ m : GL (Fin 2) (v.adicCompletion ℚ), reps j = placeEmbed ℚ v m := fun j =>
    exists_eq_placeEmbed_of_mem_doubleCoset v (hsys.mem_doubleCoset j)
  have H := AutomorphicForm.heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps ℚ v
    (sphericalImage v) (placeEmbed_map_mem v) reps hsys hpure h hsph a ⟨reps, hsys, hsum⟩ f hsupp
    hint (fun _ : Fin 1 => (1 : AdelicGL2 (𝓞 ℚ) ℚ)) (fun _ => (1 : ℂ))
    (fun _ xv => by simp)
  obtain ⟨H₁, -, -⟩ := H
  simpa only [Fin.sum_univ_one, one_mul, mul_one] using H₁ kv g

private theorem rightConv_mul_left_eq_of_forall (h f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (γ : AdelicGL2 (𝓞 ℚ) ℚ)
    (hγ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, h (γ * g) = h g) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    rightConv ℚ h f (γ * g) = rightConv ℚ h f g := by
  rw [← rightConv_comp_mul_left]
  exact congrFun (congrArg (fun φ => rightConv ℚ φ f) (funext hγ)) g

private theorem rightConv_mul_left_eq_mul_of_forall (h f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (z : AdelicGL2 (𝓞 ℚ) ℚ)
    (c : ℂ) (hz : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, h (z * g) = c * h g) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    rightConv ℚ h f (z * g) = c * rightConv ℚ h f g := by
  rw [← rightConv_comp_mul_left, rightConv_apply, rightConv_apply, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hz, mul_assoc]

end HeckeThroughConv
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end HeckeThroughConv
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

section IntermediateLevel

set_option autoImplicit false

p2m_open "NumberField IsDedekindDomain AutomorphicForm~continuous_unipotentGL2 P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm AutomorphicForm.SmoothCusp LocalGL2 AdelicDock"
open NumberField.AdelicLevel HeckeIntegralSeam CosetSystemLevel

namespace IntermediateLevel

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private theorem integralImage_eq :
    integralImage F v =
      (integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F)).map
        ((finEmbed (𝓞 F) F).comp (localEmbed (𝓞 F) F v)) :=
  rfl

private theorem isHeckeCosetSystem_of_le_of_le {N : Ideal (𝓞 F)} {V : Subgroup (AdelicGL2 (𝓞 F) F)}
    (hUV : integralImage F v ≤ V) (hVN : V ≤ levelGroup F N) {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ localImage F v)
    {ι : Type*} {reps : ι → AdelicGL2 (𝓞 F) F} (hsys : IsHeckeCosetSystem (integralImage F v) g reps) :
    IsHeckeCosetSystem V g reps :=
  isHeckeCosetSystem_of_decomp (integralImage F v) V (V ⊓ (componentAt F v).ker) (localImage F v) g reps hsys
    hUV inf_le_left
    (fun x hx => by
      have hxN : x ∈ levelGroup F N := hVN hx
      have huU : embedAt F v (componentAt F v x) ∈ integralImage F v :=
        ⟨_, componentAt_mem_integralSubgroup_of_mem_levelOne F v hxN.1, rfl⟩
      refine ⟨embedAt F v (componentAt F v x), huU, (embedAt F v (componentAt F v x))⁻¹ * x,
        ⟨V.mul_mem (V.inv_mem (hUV huU)) hx, ?_⟩, by group⟩
      show componentAt F v ((embedAt F v (componentAt F v x))⁻¹ * x) = 1
      rw [map_mul, map_inv, componentAt_embedAt, inv_mul_cancel])
    (fun c hc => awayPart_commute F v ⟨hVN hc.1, hc.2⟩ hg)
    (fun c hc u hu => awayPart_commute F v ⟨hVN hc.1, hc.2⟩ (integralImage_le_localImage F v hu))
    (integralImage_le_localImage F v) hg
    (fun x hxV hxL => mem_integralImage_of_mem_levelGroup_of_mem_localImage F v (hVN hxV) hxL)

private theorem isHeckeCosetEigenfunctionAt_of_le_of_le {N : Ideal (𝓞 F)}
    {V : Subgroup (AdelicGL2 (𝓞 F) F)} (hUV : integralImage F v ≤ V) (hVN : V ≤ levelGroup F N)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} {a : ℂ}
    (hφ : IsHeckeCosetEigenfunctionAt F (integralImage F v) (heckeGen (𝓞 F) F v) v φ a) :
    IsHeckeCosetEigenfunctionAt F V (heckeGen (𝓞 F) F v) v φ a := by
  obtain ⟨reps, hsys, hsum⟩ := hφ
  exact ⟨reps, isHeckeCosetSystem_of_le_of_le F v hUV hVN
    (exists_isHeckeCosetSystem_integralImage_heckeGen F v).1 hsys, hsum⟩

private theorem principalGroup_le_levelGroup (N : Ideal (𝓞 F)) :
    principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F ≤ levelGroup F N := by
  show principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F ≤ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F
  exact inf_le_inf_right _ (principalLevel_le_levelOne (𝓞 F) F N)

private theorem isHeckeCosetEigenfunctionAt_principalLevel {N : Ideal (𝓞 F)}
    (hUV : integralImage F v ≤ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} {a : ℂ}
    (hφ : IsHeckeCosetEigenfunctionAt F (integralImage F v) (heckeGen (𝓞 F) F v) v φ a) :
    IsHeckeCosetEigenfunctionAt F (principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (heckeGen (𝓞 F) F v) v
      φ a :=
  isHeckeCosetEigenfunctionAt_of_le_of_le F v hUV (principalGroup_le_levelGroup F N) hφ

end IntermediateLevel
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end IntermediateLevel
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

section PrincipalToLevelOne

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
p2m_open "AutomorphicForm~continuous_unipotentGL2 P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open MeasureTheory

noncomputable section

namespace PrincipalToLevelOne

private theorem centreCutSiegelSet_subset_of_le_of_sq_le {c c' u u' d₁ d₂ : ℝ} (hc : c' ≤ c) (hu : u ^ 2 ≤ u' ^ 2) :
    centreCutSiegelSet ℚ c u d₁ d₂ ⊆ centreCutSiegelSet ℚ c' u' d₁ d₂ :=
  fun _ hg => ⟨hg.1, fun w => hc.trans (hg.2.1 w), fun w => (hg.2.2.1 w).trans hu, hg.2.2.2⟩

open Classical in

private abbrev enlargedWindow (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) : Set (AdelicGL2 (𝓞 ℚ) ℚ) :=
  ⋃ x ∈ insert (1 : AdelicGL2 (𝓞 ℚ) ℚ) T,
    (· * x) '' centreCutSiegelSet ℚ (min c (Real.sqrt 3 / 2)) (max |u| (1 / 2)) d₁ d₂

private theorem sq_le_sq_max_abs (u : ℝ) : u ^ 2 ≤ (max |u| (1 / 2)) ^ 2 := by
  nlinarith [abs_nonneg u, le_max_left |u| (1 / 2 : ℝ), sq_abs u]

open Classical in
private theorem window_subset_enlargedWindow (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) :
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) ⊆ enlargedWindow c u d₁ d₂ T :=
  Set.iUnion₂_subset fun x hx =>
    Set.subset_iUnion₂_of_subset x (Finset.mem_insert_of_mem hx)
      (Set.image_mono (centreCutSiegelSet_subset_of_le_of_sq_le (min_le_left _ _) (sq_le_sq_max_abs u)))

open Classical in
private theorem coversModCentre_enlargedWindow (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd₁ : 0 < d₁) (hd : d₁ < d₂) : CoversModCentre ℚ (enlargedWindow c u d₁ d₂ T) :=
  (centreCutSiegelSet_coversModCentre_rat (min_le_right _ _) (le_max_right _ _) (hd₁.trans hd) hd.le).mono
    fun g hg => Set.mem_iUnion₂.2 ⟨1, Finset.mem_insert_self _ _, g, hg, mul_one g⟩

private theorem isIsotypicCuspFormAt_of_forall_notMem_eq {pins : CarrierPins ℚ} {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 ℚ)}
    {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {Φ Ψ : HeckeEigensystem ℚ ℂ} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (h : IsIsotypicCuspFormAt ℚ pins ξ N S Φ φ)
    (ha : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → Ψ.a v = Φ.a v)
    (hb : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → Ψ.b v = Φ.b v) :
    IsIsotypicCuspFormAt ℚ pins ξ N S Ψ φ where
  smoothCusp := h.smoothCusp
  continuous := h.continuous
  level_invariant := h.level_invariant
  hecke_eigen v hv := by rw [ha v hv]; exact h.hecke_eigen v hv
  central_eigen v hv g := by
    have h1 := h.central_eigen v hv g
    have h2 : Ψ.toRawCentral.b v = Φ.toRawCentral.b v := by
      show (HeckeEigensystem.cNorm v)⁻¹ * Ψ.b v = (HeckeEigensystem.cNorm v)⁻¹ * Φ.b v
      rw [hb v hv]
    rw [h2]; exact h1

private theorem isIsotypicCuspFormAt_productionPinsOf_of_subset {D D' : Set (AdelicGL2 (𝓞 ℚ) ℚ)} (hDD' : D ⊆ D')
    (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (Bx : Set (AdeleRing (𝓞 ℚ) ℚ))
    {ξ : (productionPinsOf ℚ D' U gen Bx).Z →* ℂˣ} {N : Ideal (𝓞 ℚ)} {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
    {Φ : HeckeEigensystem ℚ ℂ} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (h : IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ D' U gen Bx) ξ N S Φ φ) :
    IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ D U gen Bx) ξ N S Φ φ where
  smoothCusp := by
    obtain ⟨⟨hauto, hcusp⟩, hkf⟩ := h.smoothCusp
    refine ⟨⟨?_, hcusp⟩, hkf⟩
    unfold IsAutomorphicFnAt at hauto ⊢
    rw [lsXiMemberAt_iff] at hauto ⊢
    exact ⟨hauto.1, hauto.2.mono_measure (Measure.restrict_mono hDD' le_rfl)⟩
  continuous := h.continuous
  level_invariant := h.level_invariant
  hecke_eigen := h.hecke_eigen
  central_eigen := h.central_eigen

private theorem exists_level_isArithGenuineCuspRealizable_of_isIsotypicCuspFormAt_principalLevel
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (a b : HeightOneSpectrum (𝓞 ℚ) → ℂ) (S₁ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ξ₀ : (productionPinsOf ℚ (enlargedWindow c u d₁ d₂ T)
        (fun N => principalLevel (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)).Z →* ℂˣ)
    (N' : Ideal (𝓞 ℚ)) (hN' : N' ≠ ⊥) (hN'S : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.asIdeal ∣ N' → v ∈ S₁)
    (φ₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hφ₁ : IsIsotypicCuspFormAt ℚ
      (productionPinsOf ℚ (enlargedWindow c u d₁ d₂ T)
        (fun N => principalLevel (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)) ξ₀ N' S₁ ⟨N', hN', a, b⟩ φ₁)
    (hφ₁0 : φ₁ ≠ 0) :
    ∃ (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥), (∀ v : HeightOneSpectrum (𝓞 ℚ), v.asIdeal ∣ N → v ∈ S₁) ∧
      IsArithGenuineCuspRealizable ℚ
        (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        ⟨N, hN, a, b⟩ := by
  classical
  have hc₀ : 0 < min c (Real.sqrt 3 / 2) := lt_min hc (by positivity)
  have hcov := coversModCentre_enlargedWindow c u d₁ d₂ T hd₁ hd

  let π₀ : HeckeEigensystem ℚ ℂ :=
    ⟨N', hN', fun v => if v ∈ S₁ then 0 else a v, fun v => if v ∈ S₁ then 0 else b v⟩
  have hφ₁' := isIsotypicCuspFormAt_of_forall_notMem_eq (Ψ := π₀) hφ₁
    (fun v hv => by simp [π₀, hv]) (fun v hv => by simp [π₀, hv])
  have hπ₀ : π₀ ∈ cuspClasses ℚ
      (productionPinsOf ℚ (enlargedWindow c u d₁ d₂ T)
        (fun N => principalLevel (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)) ξ₀ N' S₁ :=
    ⟨rfl, fun v hv => by simp [π₀, hv],
      (isotypicCuspSubmodule_ne_bot_iff ℚ _ ξ₀ N' S₁ π₀).2 ⟨φ₁, hφ₁', hφ₁0⟩⟩
  obtain ⟨N'', π'', hN'', hN''S, hπ'', hagree⟩ :=
    exists_mem_cuspClasses_levelOne_of_mem_cuspClasses_principalLevel ℚ (min c (Real.sqrt 3 / 2))
      (max |u| (1 / 2)) d₁ d₂ _ hc₀ hd₁ hd hcov S₁ ξ₀ N' hN'S π₀ hπ₀
  obtain ⟨φ, hφ, hφ0⟩ := exists_isIsotypicCuspFormAt_ne_zero_of_mem_cuspClasses hπ''
  have hφ' := isIsotypicCuspFormAt_of_forall_notMem_eq (Ψ := ⟨N'', hN'', a, b⟩) hφ
    (fun v hv => by rw [(hagree v hv).1]; simp [π₀, hv]) (fun v hv => by rw [(hagree v hv).2]; simp [π₀, hv])
  have hφD := isIsotypicCuspFormAt_productionPinsOf_of_subset (window_subset_enlargedWindow c u d₁ d₂ T)
    (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ) hφ'
  exact ⟨N'', hN'', hN''S, hφD.isArithGenuineCuspRealizable hφ0⟩

end PrincipalToLevelOne
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end PrincipalToLevelOne
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

section AdelicNeighbourhood

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField NumberField.AdelicLevel AutomorphicForm~continuous_unipotentGL2 P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm Filter"
open scoped Topology

namespace AdelicNeighbourhood

section Generic

variable {R : Type*} [TopologicalSpace R]

private theorem exists_entry_box {a : Matrix (Fin 2) (Fin 2) R} {M : Set (Matrix (Fin 2) (Fin 2) R)} (hM : M ∈ 𝓝 a) :
    ∃ E : Fin 2 → Fin 2 → Set R, (∀ i j, E i j ∈ 𝓝 (a i j)) ∧
      ∀ m : Matrix (Fin 2) (Fin 2) R, (∀ i j, m i j ∈ E i j) → m ∈ M := by
  have h1 : (M : Set (Fin 2 → Fin 2 → R)) ∈ pi fun i : Fin 2 => 𝓝 (a i) :=
    Eq.mp (congrArg (fun l => (M : Set (Fin 2 → Fin 2 → R)) ∈ l) (nhds_pi (A := fun _ : Fin 2 => Fin 2 → R) (a := a)))
      hM
  obtain ⟨I, -, t, ht, htM⟩ := mem_pi.mp h1
  have hrow : ∀ i : Fin 2, ∃ E : Fin 2 → Set R, (∀ j, E j ∈ 𝓝 (a i j)) ∧
      ∀ r : Fin 2 → R, (∀ j, r j ∈ E j) → r ∈ t i := by
    intro i
    have h2 : t i ∈ pi fun j : Fin 2 => 𝓝 (a i j) := by
      rw [← nhds_pi]
      exact ht i
    obtain ⟨J, -, E, hE, hEt⟩ := mem_pi.mp h2
    exact ⟨E, hE, fun r hr => hEt fun j _ => hr j⟩
  choose E hE hEt using hrow
  exact ⟨E, hE, fun m hm => htM fun i _ => hEt i (m i) (hm i)⟩

variable [CommRing R]

private theorem exists_matrix_nhds_of_nhds_one {V : Set (GL (Fin 2) R)} (hV : V ∈ 𝓝 1) :
    ∃ M ∈ 𝓝 (1 : Matrix (Fin 2) (Fin 2) R), ∀ g : GL (Fin 2) R, g.val ∈ M → (g⁻¹).val ∈ M → g ∈ V := by
  rw [(Units.isInducing_embedProduct (M := Matrix (Fin 2) (Fin 2) R)).nhds_eq_comap, mem_comap] at hV
  obtain ⟨U, hU, hUV⟩ := hV
  rw [map_one] at hU
  have hU' : U ∈ 𝓝 ((1 : Matrix (Fin 2) (Fin 2) R), (1 : (Matrix (Fin 2) (Fin 2) R)ᵐᵒᵖ)) := hU
  obtain ⟨M₁, hM₁, O₂, hO₂, hprod⟩ := mem_nhds_prod_iff.mp hU'
  have hM₂ : MulOpposite.op ⁻¹' O₂ ∈ 𝓝 (1 : Matrix (Fin 2) (Fin 2) R) := by
    have h : MulOpposite.op ⁻¹' O₂ ∈
        comap (MulOpposite.op : Matrix (Fin 2) (Fin 2) R → (Matrix (Fin 2) (Fin 2) R)ᵐᵒᵖ) (𝓝 1) :=
      preimage_mem_comap hO₂
    rwa [MulOpposite.comap_op_nhds, MulOpposite.unop_one] at h
  refine ⟨M₁ ∩ MulOpposite.op ⁻¹' O₂, inter_mem hM₁ hM₂, fun g hg hg' => hUV ?_⟩
  exact hprod (show (g.val, MulOpposite.op (g⁻¹).val) ∈ M₁ ×ˢ O₂ from ⟨hg.1, hg'.2⟩)

private theorem glBox_mem_nhds_one (A : Fin 2 → Fin 2 → Set R)
    (hA : ∀ i j, A i j ∈ 𝓝 ((1 : Matrix (Fin 2) (Fin 2) R) i j)) :
    {g : GL (Fin 2) R | ∀ i j, g.val i j ∈ A i j ∧ (g⁻¹).val i j ∈ A i j} ∈ 𝓝 (1 : GL (Fin 2) R) := by
  have hval : ∀ i j, ∀ᶠ g : GL (Fin 2) R in 𝓝 1, g.val i j ∈ A i j := fun i j =>
    (Units.continuous_val.matrix_elem i j).continuousAt.preimage_mem_nhds (by simpa using hA i j)
  have hinv : ∀ i j, ∀ᶠ g : GL (Fin 2) R in 𝓝 1, (g⁻¹).val i j ∈ A i j := fun i j =>
    (Units.continuous_coe_inv.matrix_elem i j).continuousAt.preimage_mem_nhds (by simpa using hA i j)
  exact eventually_all.2 fun i => eventually_all.2 fun j => (hval i j).and (hinv i j)

end Generic
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

section Adelic

variable (F : Type*) [Field F] [NumberField F]

private theorem one_entry_fst (i j : Fin 2) :
    ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1
      = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j := by
  have h := glArch_apply (g := (1 : GL (Fin 2) (AdeleRing (𝓞 F) F))) (i := i) (j := j)
  rw [map_one] at h
  exact h.symm

private theorem one_entry_snd_apply (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2) :
    (((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 : FiniteAdeleRing (𝓞 F) F) v
      = (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j := by
  have h1 := glFin_apply (g := (1 : GL (Fin 2) (AdeleRing (𝓞 F) F))) (i := i) (j := j)
  rw [map_one] at h1
  have h2 := finComponent_apply (v := v) (g := (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) (i := i) (j := j)
  rw [map_one] at h2
  exact (congrArg (fun b : FiniteAdeleRing (𝓞 F) F => b v) h1.symm).trans h2.symm

private theorem exists_nhds_one_unpacking (V : Set (GL (Fin 2) (AdeleRing (𝓞 F) F))) (hV : V ∈ 𝓝 1) :
    ∃ Varch ∈ 𝓝 (1 : GL (Fin 2) (InfiniteAdeleRing F)), ∃ T : Finset (HeightOneSpectrum (𝓞 F)),
      ∃ W : ∀ v : HeightOneSpectrum (𝓞 F), Set (GL (Fin 2) (v.adicCompletion F)), (∀ v, W v ∈ 𝓝 1) ∧
        ∀ y : GL (Fin 2) (AdeleRing (𝓞 F) F), glArch (𝓞 F) F y ∈ Varch →
          (∀ v ∈ T, finComponent (𝓞 F) F v (glFin (𝓞 F) F y) ∈ W v) →
          (∀ w ∉ T, finComponent (𝓞 F) F w (glFin (𝓞 F) F y) ∈ localIntegralSet F w) → y ∈ V := by
  obtain ⟨M, hM, hMV⟩ := exists_matrix_nhds_of_nhds_one hV
  obtain ⟨E, hE, hEM⟩ := exists_entry_box hM
  have hsplit : ∀ i j, ∃ A : Set (InfiniteAdeleRing F),
      A ∈ 𝓝 ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 ∧
      ∃ B : Set (FiniteAdeleRing (𝓞 F) F), B ∈ 𝓝 ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 ∧
        ∀ a : AdeleRing (𝓞 F) F, a.1 ∈ A → a.2 ∈ B → a ∈ E i j := by
    intro i j
    have h : E i j ∈ 𝓝 (((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1,
        ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2) := hE i j
    obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp h
    exact ⟨A, hA, B, hB, fun a ha hb => hAB (Set.mk_mem_prod ha hb)⟩
  choose A hA B hB hABE using hsplit
  have hfin : ∀ i j, ∃ s : ∀ w : HeightOneSpectrum (𝓞 F), Set (w.adicCompletion F),
      (∀ w, s w ∈ 𝓝 ((((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 : FiniteAdeleRing (𝓞 F) F) w)) ∧
      {w | s w ≠ (w.adicCompletionIntegers F : Set (w.adicCompletion F))}.Finite ∧
      ∀ b : FiniteAdeleRing (𝓞 F) F, (∀ w, b w ∈ s w) → b ∈ B i j := by
    intro i j
    obtain ⟨s, hs, hsf, hsB⟩ := (RestrictedProduct.mem_nhds_iff_of_cofinite
      (G := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) (C := fun w => w.adicCompletionIntegers F)
      (fun w => Valued.isOpen_valuationSubring (w.adicCompletion F))).mp (hB i j)
    refine ⟨s, hs, eventually_cofinite.mp hsf, fun b hb => ?_⟩
    obtain ⟨b', hb'B, hb'b⟩ := hsB fun w _ => hb w
    have hbb : b' = b := RestrictedProduct.ext _ _ fun w => congrFun hb'b w
    exact Set.mem_of_eq_of_mem hbb.symm hb'B
  choose s hs hsfin hsB using hfin
  have hX : (⋃ i, ⋃ j, {w : HeightOneSpectrum (𝓞 F) |
      s i j w ≠ (w.adicCompletionIntegers F : Set (w.adicCompletion F))}).Finite :=
    Set.finite_iUnion fun i => Set.finite_iUnion fun j => hsfin i j
  refine ⟨_, glBox_mem_nhds_one A fun i j => (one_entry_fst F i j) ▸ hA i j, hX.toFinset, _,
    fun v => glBox_mem_nhds_one (fun i j => s i j v) fun i j => (one_entry_snd_apply F v i j) ▸ hs i j v, ?_⟩
  intro y hyarch hyT hyint
  have hent : ∀ w : HeightOneSpectrum (𝓞 F), ∀ i j,
      ((y.val i j).2 : FiniteAdeleRing (𝓞 F) F) w ∈ s i j w ∧
        (((y⁻¹).val i j).2 : FiniteAdeleRing (𝓞 F) F) w ∈ s i j w := by
    intro w i j
    by_cases hw : w ∈ hX.toFinset
    · exact hyT w hw i j
    · have hsw : ∀ i j, s i j w = (w.adicCompletionIntegers F : Set (w.adicCompletion F)) := by
        intro i j
        by_contra h
        exact hw (hX.mem_toFinset.mpr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, h⟩⟩))
      have hloc := (mem_localIntegralSet F w).mp (hyint w hw)
      rw [hsw i j]
      exact ⟨hloc.1 i j, hloc.2 i j⟩
  exact hMV y (hEM _ fun i j => hABE i j _ (hyarch i j).1 (hsB i j _ fun w => (hent w i j).1))
    (hEM _ fun i j => hABE i j _ (hyarch i j).2 (hsB i j _ fun w => (hent w i j).2))

end Adelic
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end AdelicNeighbourhood
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end AdelicNeighbourhood
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

section LocalCongruence

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm~continuous_unipotentGL2 P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm"

noncomputable section

namespace LocalCongruence

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (N : Ideal (𝓞 K))

private def localBall : Set (v.adicCompletion K) := {y | Valued.v y ≤ AdelicLevel.idealBound (𝓞 K) N v}

private theorem mem_localBall {y : v.adicCompletion K} :
    y ∈ localBall K v N ↔ Valued.v y ≤ AdelicLevel.idealBound (𝓞 K) N v := Iff.rfl

variable {N} in
private theorem isOpen_localBall (hN : N ≠ ⊥) : IsOpen (localBall K v N) :=
  AdelicLevel.isOpen_setOf_valued_le_idealBound v hN

private theorem isClosed_localBall : IsClosed (localBall K v N) :=
  AdelicLevel.isClosed_setOf_valued_le_idealBound v N

private theorem zero_mem_localBall : (0 : v.adicCompletion K) ∈ localBall K v N := by
  rw [mem_localBall, map_zero]
  exact zero_le'

private
theorem localBall_subset_integers : localBall K v N ⊆ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  fun _ hy => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr
    (hy.trans (AdelicLevel.idealBound_le_one N v))

variable {K v N}

private theorem add_mem_localBall {y z : v.adicCompletion K} (hy : y ∈ localBall K v N) (hz : z ∈ localBall K v N) :
    y + z ∈ localBall K v N := by
  rw [mem_localBall] at hy hz ⊢
  exact (Valuation.map_add _ _ _).trans (max_le hy hz)

private theorem mul_mem_localBall_of_integers_left {z y : v.adicCompletion K} (hz : z ∈ v.adicCompletionIntegers K)
    (hy : y ∈ localBall K v N) : z * y ∈ localBall K v N := by
  rw [mem_localBall] at hy ⊢
  rw [map_mul]
  calc Valued.v z * Valued.v y ≤ 1 * AdelicLevel.idealBound (𝓞 K) N v :=
        mul_le_mul' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hz) hy
    _ = AdelicLevel.idealBound (𝓞 K) N v := one_mul _

private theorem mul_mem_localBall_of_integers_right {y z : v.adicCompletion K} (hy : y ∈ localBall K v N)
    (hz : z ∈ v.adicCompletionIntegers K) : y * z ∈ localBall K v N := by
  rw [mul_comm]
  exact mul_mem_localBall_of_integers_left hz hy

private theorem localBall_eq_integers (hN : N ≠ ⊥) (hv : ¬ v.asIdeal ∣ N) :
    localBall K v N = (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  ext y
  rw [mem_localBall, AdelicLevel.idealBound_eq_one_of_not_dvd hN hv, SetLike.mem_coe,
    HeightOneSpectrum.mem_adicCompletionIntegers]

variable (K v N)

private def congruentMatrices : Set (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
  {m | ∀ i j, m i j - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ localBall K v N}

private theorem congruentMatrices_eq_preimage :
    congruentMatrices K v N =
      (fun m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) => m - 1) ⁻¹' integralMatrixSet (localBall K v N) := by
  ext m
  simp only [congruentMatrices, integralMatrixSet, Set.mem_setOf_eq, Set.mem_preimage, Matrix.sub_apply]

private theorem isClosed_integralMatrixSet_of_isClosed {U : Set (v.adicCompletion K)} (hU : IsClosed U) :
    IsClosed (integralMatrixSet U) := by
  rw [integralMatrixSet_eq_pi]
  exact isClosed_set_pi fun _ _ => isClosed_set_pi fun _ _ => hU

variable {N} in
private theorem isOpen_congruentMatrices (hN : N ≠ ⊥) : IsOpen (congruentMatrices K v N) := by
  rw [congruentMatrices_eq_preimage]
  exact (isOpen_integralMatrixSet (isOpen_localBall K v hN)).preimage (continuous_id.sub continuous_const)

private theorem isClosed_congruentMatrices : IsClosed (congruentMatrices K v N) := by
  rw [congruentMatrices_eq_preimage]
  exact (isClosed_integralMatrixSet_of_isClosed K v (isClosed_localBall K v N)).preimage
    (continuous_id.sub continuous_const)

private
theorem one_mem_congruentMatrices : (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ∈ congruentMatrices K v N :=
  fun _ _ => by rw [sub_self]; exact zero_mem_localBall K v N

private theorem one_apply_mem_integers (i j : Fin 2) :
    (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K := by
  by_cases h : i = j
  · subst h; rw [Matrix.one_apply_eq]; exact one_mem _
  · rw [Matrix.one_apply_ne h]; exact zero_mem _

variable {K v N}

private theorem apply_mem_integers_of_mem_congruentMatrices {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)}
    (hm : m ∈ congruentMatrices K v N) (i j : Fin 2) : m i j ∈ v.adicCompletionIntegers K := by
  have h : m i j = (m i j - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j)
      + (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := (sub_add_cancel _ _).symm
  rw [h]
  exact add_mem (localBall_subset_integers K v N (hm i j)) (one_apply_mem_integers K v i j)

private theorem mul_mem_congruentMatrices {m n : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)}
    (hm : m ∈ congruentMatrices K v N) (hn : n ∈ congruentMatrices K v N) : m * n ∈ congruentMatrices K v N := by
  intro i j
  have key : (m * n) i j - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
      (∑ k, (m i k - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i k) * n k j)
        + (n i j - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) := by
    have h1 : ∑ k, (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i k * n k j = n i j := by
      simpa [Matrix.mul_apply] using congrFun (congrFun (Matrix.one_mul n) i) j
    simp only [Matrix.mul_apply, sub_mul, Finset.sum_sub_distrib, h1]
    ring
  rw [key, Fin.sum_univ_two]
  exact add_mem_localBall
    (add_mem_localBall
      (mul_mem_localBall_of_integers_right (hm i 0) (apply_mem_integers_of_mem_congruentMatrices hn 0 j))
      (mul_mem_localBall_of_integers_right (hm i 1) (apply_mem_integers_of_mem_congruentMatrices hn 1 j)))
    (hn i j)

variable (K v N)

private def congruenceSet : Set (GL (Fin 2) (v.adicCompletion K)) :=
  {g | (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ∈ congruentMatrices K v N ∧
    ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ∈ congruentMatrices K v N}

private theorem mem_congruenceSet {g : GL (Fin 2) (v.adicCompletion K)} :
    g ∈ congruenceSet K v N ↔
      (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ∈ congruentMatrices K v N ∧
        ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
          ∈ congruentMatrices K v N :=
  Iff.rfl

private theorem congruenceSet_eq_preimage :
    congruenceSet K v N = (Units.embedProduct (Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ⁻¹'
      (congruentMatrices K v N ×ˢ (MulOpposite.op '' congruentMatrices K v N)) := by
  ext g
  simp only [congruenceSet, Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod,
    Set.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, _, h2, rfl⟩
  · rintro ⟨h1, m, hm, hm'⟩
    refine ⟨h1, ?_⟩
    have : m = ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
      MulOpposite.op_injective hm'
    rw [← this]
    exact hm

variable {N} in
private theorem isOpen_congruenceSet (hN : N ≠ ⊥) : IsOpen (congruenceSet K v N) := by
  rw [congruenceSet_eq_preimage]
  exact ((isOpen_congruentMatrices K v hN).prod
    (MulOpposite.opHomeomorph.isOpenMap _ (isOpen_congruentMatrices K v hN))).preimage Units.continuous_embedProduct

private theorem isClosed_congruenceSet : IsClosed (congruenceSet K v N) := by
  rw [congruenceSet_eq_preimage]
  exact ((isClosed_congruentMatrices K v N).prod
    (MulOpposite.opHomeomorph.isClosedMap _ (isClosed_congruentMatrices K v N))).preimage
    Units.continuous_embedProduct

private theorem one_mem_congruenceSet : (1 : GL (Fin 2) (v.adicCompletion K)) ∈ congruenceSet K v N := by
  rw [mem_congruenceSet, inv_one, Units.val_one]
  exact ⟨one_mem_congruentMatrices K v N, one_mem_congruentMatrices K v N⟩

private theorem congruenceSet_subset_localIntegralSet : congruenceSet K v N ⊆ localIntegralSet K v := by
  intro g hg
  rw [mem_congruenceSet] at hg
  rw [mem_localIntegralSet]
  exact ⟨fun i j => apply_mem_integers_of_mem_congruentMatrices hg.1 i j,
    fun i j => apply_mem_integers_of_mem_congruentMatrices hg.2 i j⟩

private theorem isCompact_congruenceSet : IsCompact (congruenceSet K v N) :=
  (isCompact_localIntegralSet K v).of_isClosed_subset (isClosed_congruenceSet K v N)
    (congruenceSet_subset_localIntegralSet K v N)

variable {K v N}

private theorem mul_mem_congruenceSet {x g : GL (Fin 2) (v.adicCompletion K)} (hx : x ∈ congruenceSet K v N)
    (hg : g ∈ congruenceSet K v N) : x * g ∈ congruenceSet K v N := by
  rw [mem_congruenceSet] at hx hg ⊢
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul]
    exact mul_mem_congruentMatrices hx.1 hg.1
  · rw [mul_inv_rev, Units.val_mul]
    exact mul_mem_congruentMatrices hg.2 hx.2

private theorem inv_mem_congruenceSet {x : GL (Fin 2) (v.adicCompletion K)} (hx : x ∈ congruenceSet K v N) :
    x⁻¹ ∈ congruenceSet K v N := by
  rw [mem_congruenceSet] at hx ⊢
  rw [inv_inv]
  exact ⟨hx.2, hx.1⟩

private theorem mul_mem_congruenceSet_iff {x : GL (Fin 2) (v.adicCompletion K)} (hx : x ∈ congruenceSet K v N)
    (g : GL (Fin 2) (v.adicCompletion K)) : x * g ∈ congruenceSet K v N ↔ g ∈ congruenceSet K v N := by
  refine ⟨fun h => ?_, fun h => mul_mem_congruenceSet hx h⟩
  have := mul_mem_congruenceSet (inv_mem_congruenceSet hx) h
  rwa [inv_mul_cancel_left] at this

private theorem indicator_congruenceSet_mul_left {x : GL (Fin 2) (v.adicCompletion K)} (hx : x ∈ congruenceSet K v N)
    (g : GL (Fin 2) (v.adicCompletion K)) :
    (congruenceSet K v N).indicator (fun _ => (1 : ℂ)) (x * g) =
      (congruenceSet K v N).indicator (fun _ => (1 : ℂ)) g := by
  by_cases hg : g ∈ congruenceSet K v N
  · rw [Set.indicator_of_mem ((mul_mem_congruenceSet_iff hx g).mpr hg), Set.indicator_of_mem hg]
  · rw [Set.indicator_of_notMem (fun h' => hg ((mul_mem_congruenceSet_iff hx g).mp h')), Set.indicator_of_notMem hg]

variable (K v N)

private theorem isLocalTestFn_indicator_congruenceSet (hN : N ≠ ⊥) :
    IsLocalTestFn K v ((congruenceSet K v N).indicator fun _ => (1 : ℂ)) :=
  ⟨isLocallyConstant_indicator_one (isOpen_congruenceSet K v hN) (isClosed_congruenceSet K v N),
    HasCompactSupport.intro (isCompact_congruenceSet K v N) fun _ hg => by simp [hg]⟩

private theorem mem_congruentMatrices_iff_of_not_dvd (hN : N ≠ ⊥) (hv : ¬ v.asIdeal ∣ N)
    {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)} :
    m ∈ congruentMatrices K v N ↔ ∀ i j, m i j ∈ v.adicCompletionIntegers K := by
  refine ⟨fun hm i j => apply_mem_integers_of_mem_congruentMatrices hm i j, fun hm i j => ?_⟩
  show m i j - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ localBall K v N
  rw [localBall_eq_integers hN hv, SetLike.mem_coe]
  exact sub_mem (hm i j) (one_apply_mem_integers K v i j)

private theorem congruenceSet_eq_localIntegralSet_of_not_dvd (hN : N ≠ ⊥) (hv : ¬ v.asIdeal ∣ N) :
    congruenceSet K v N = localIntegralSet K v := by
  ext g
  rw [mem_congruenceSet, mem_congruentMatrices_iff_of_not_dvd K v N hN hv,
    mem_congruentMatrices_iff_of_not_dvd K v N hN hv]
  exact Iff.rfl

end LocalCongruence
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end LocalCongruence
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

section CongruenceBasis

set_option autoImplicit false

open IsDedekindDomain NumberField Topology Filter

noncomputable section

namespace CongruenceBasis

private theorem exists_exp_neg_lt {c : WithZero (Multiplicative ℤ)} (hc : c ≠ 0) :
    ∃ n : ℕ, WithZero.exp (-(n : ℤ)) < c := by
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, c = WithZero.exp m := ⟨_, (WithZero.exp_log hc).symm⟩
  refine ⟨(-m).toNat + 1, ?_⟩
  rw [WithZero.exp_lt_exp]
  omega

private
theorem exists_matrix_nhds {R : Type*} [CommRing R] [TopologicalSpace R] {n : Type*} [Fintype n] [DecidableEq n]
    {W : Set (GL n R)} (hW : W ∈ 𝓝 (1 : GL n R)) :
    ∃ M ∈ 𝓝 (1 : Matrix n n R), ∀ g : GL n R,
      (g : Matrix n n R) ∈ M → ((g⁻¹ : GL n R) : Matrix n n R) ∈ M → g ∈ W := by
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hW
  obtain ⟨P, hP, hPW⟩ := hW
  rw [Units.embedProduct_apply, inv_one, Units.val_one] at hP
  obtain ⟨M₁, hM₁, M₂, hM₂, hsub⟩ := mem_nhds_prod_iff.mp hP
  have hM₂' : (MulOpposite.op ⁻¹' M₂ : Set (Matrix n n R)) ∈ 𝓝 (1 : Matrix n n R) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hM₂
  refine ⟨M₁ ∩ MulOpposite.op ⁻¹' M₂, Filter.inter_mem hM₁ hM₂', fun g hg hg' => hPW ?_⟩
  rw [Set.mem_preimage, Units.embedProduct_apply]
  exact hsub (Set.mk_mem_prod hg.1 hg'.2)

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private
theorem exists_nat_forall_valued_le_imp_mem {U : Set (v.adicCompletion K)} (hU : U ∈ 𝓝 (0 : v.adicCompletion K)) :
    ∃ n : ℕ, ∀ y : v.adicCompletion K, Valued.v y ≤ WithZero.exp (-(n : ℤ)) → y ∈ U := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hU
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ (0 : WithZero (Multiplicative ℤ)) :=
    (map_ne_zero MonoidWithZeroHom.ValueGroup₀.embedding).mpr γ.ne_zero
  obtain ⟨n, hn⟩ := exists_exp_neg_lt hne
  refine ⟨n, fun y hy => hγ ?_⟩
  rw [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
  exact lt_of_le_of_lt hy hn

private theorem idealBound_le_exp_neg_of_pow_dvd {N : Ideal (𝓞 K)} (hN : N ≠ ⊥) {n : ℕ} (h : v.asIdeal ^ n ∣ N) :
    AdelicLevel.idealBound (𝓞 K) N v ≤ WithZero.exp (-(n : ℤ)) := by
  classical
  rw [AdelicLevel.idealBound_of_ne_bot hN, WithZero.exp_le_exp, neg_le_neg_iff]
  have hirr : Irreducible (Associates.mk v.asIdeal) := Associates.irreducible_mk.mpr v.irreducible
  have h1 := Associates.count_le_count_of_le (Associates.mk_ne_zero.mpr (show N ≠ 0 from hN)) hirr
    (Associates.mk_le_mk_of_dvd h)
  rw [Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.mpr (show v.asIdeal ≠ 0 from v.ne_bot)) hirr,
    Associates.count_self hirr, mul_one] at h1
  exact_mod_cast h1

private theorem exists_nat_congruenceSet_subset {W : Set (GL (Fin 2) (v.adicCompletion K))}
    (hW : W ∈ 𝓝 (1 : GL (Fin 2) (v.adicCompletion K))) :
    ∃ n : ℕ, ∀ N : Ideal (𝓞 K), AdelicLevel.idealBound (𝓞 K) N v ≤ WithZero.exp (-(n : ℤ)) →
      LocalCongruence.congruenceSet K v N ⊆ W := by
  obtain ⟨M, hM, hMW⟩ := exists_matrix_nhds hW
  obtain ⟨E, hE, hEM⟩ := AdelicNeighbourhood.exists_entry_box hM
  have hE0 : ∀ i j, ∃ n : ℕ, ∀ y : v.adicCompletion K, Valued.v y ≤ WithZero.exp (-(n : ℤ)) →
      y + (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ E i j := by
    intro i j
    have h : (fun y : v.adicCompletion K => y + (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ⁻¹' E i j
        ∈ 𝓝 (0 : v.adicCompletion K) := by
      refine (continuous_add_const _).continuousAt.preimage_mem_nhds ?_
      simpa only [zero_add] using hE i j
    obtain ⟨n, hn⟩ := exists_nat_forall_valued_le_imp_mem K v h
    exact ⟨n, fun y hy => hn y hy⟩
  choose nE hnE using hE0
  set n : ℕ := nE 0 0 + nE 0 1 + nE 1 0 + nE 1 1 with hn
  have hle : ∀ i j, nE i j ≤ n := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp only [hn, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> omega
  have hexp : ∀ i j, WithZero.exp (-(n : ℤ)) ≤ WithZero.exp (-(nE i j : ℤ)) := fun i j =>
    WithZero.exp_le_exp.mpr (neg_le_neg (by exact_mod_cast hle i j))
  have key : ∀ m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), ∀ N : Ideal (𝓞 K),
      AdelicLevel.idealBound (𝓞 K) N v ≤ WithZero.exp (-(n : ℤ)) → m ∈ LocalCongruence.congruentMatrices K v N →
        m ∈ M := by
    intro m N hN hm
    refine hEM m fun i j => ?_
    have hij := hm i j
    rw [LocalCongruence.mem_localBall] at hij
    have := hnE i j _ (hij.trans (hN.trans (hexp i j)))
    rwa [sub_add_cancel] at this
  refine ⟨n, fun N hN g hg => ?_⟩
  rw [LocalCongruence.mem_congruenceSet] at hg
  exact hMW g (key _ N hN hg.1) (key _ N hN hg.2)

end CongruenceBasis
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end CongruenceBasis
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

section PrincipalCongruence

set_option autoImplicit false

p2m_open "NumberField IsDedekindDomain AutomorphicForm~continuous_unipotentGL2 P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm LocalGL2 AdelicDock NumberField.AdelicLevel P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.CosetSystemLevel"

noncomputable section

namespace PrincipalCongruence

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private theorem glArch_embedAt (k : GL (Fin 2) (v.adicCompletion F)) : glArch (𝓞 F) F (embedAt F v k) = 1 :=
  glArch_finEmbed (𝓞 F) F _

private theorem finComponent_glFin_embedAt_of_ne (k : GL (Fin 2) (v.adicCompletion F)) {w : HeightOneSpectrum (𝓞 F)}
    (hw : w ≠ v) : finComponent (𝓞 F) F w (glFin (𝓞 F) F (embedAt F v k)) = 1 := by
  have he : glFin (𝓞 F) F (embedAt F v k) = localEmbed (𝓞 F) F v k := glFin_finEmbed (𝓞 F) F _
  rw [he, finComponent_localEmbed_of_ne (𝓞 F) F v k hw]

private theorem commute_embedAt_of_componentAt_eq_one {z : AdelicGL2 (𝓞 F) F} (hz : componentAt F v z = 1)
    (k : GL (Fin 2) (v.adicCompletion F)) : z * embedAt F v k = embedAt F v k * z := by
  have h1 : ∀ y : AdelicGL2 (𝓞 F) F, finComponent (𝓞 F) F v (glFin (𝓞 F) F y) = componentAt F v y := fun _ => rfl
  apply ext_of_components F
  · simp only [map_mul, glArch_embedAt, one_mul, mul_one]
  · intro w
    by_cases hw : w = v
    · rw [hw]
      simp only [h1, map_mul, hz, componentAt_embedAt, one_mul, mul_one]
    · simp only [map_mul, finComponent_glFin_embedAt_of_ne F v (hw := hw), one_mul, mul_one]

private def stripAt (x : AdelicGL2 (𝓞 F) F) : AdelicGL2 (𝓞 F) F := x * (embedAt F v (componentAt F v x))⁻¹

private theorem stripAt_mul_embedAt (x : AdelicGL2 (𝓞 F) F) : stripAt F v x * embedAt F v (componentAt F v x) = x := by
  simp [stripAt]

private theorem componentAt_stripAt (x : AdelicGL2 (𝓞 F) F) : componentAt F v (stripAt F v x) = 1 := by
  simp [stripAt, componentAt_embedAt]

private theorem stripAt_commute (x : AdelicGL2 (𝓞 F) F) (k : GL (Fin 2) (v.adicCompletion F)) :
    stripAt F v x * embedAt F v k = embedAt F v k * stripAt F v x :=
  commute_embedAt_of_componentAt_eq_one F v (componentAt_stripAt F v x) k

private theorem mem_integralSubgroup_of_mem_localIntegralSet {k : GL (Fin 2) (v.adicCompletion F)}
    (hk : k ∈ localIntegralSet F v) : k ∈ integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F) := by
  rw [mem_localIntegralSet] at hk
  exact mem_integralSubgroup_of_entries F v k hk.1 hk.2

private theorem exists_eq_mul_of_componentAt_mem {z : AdelicGL2 (𝓞 F) F}
    (hz : componentAt F v z ∈ integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F)) :
    ∃ z₁ z₂ : AdelicGL2 (𝓞 F) F, z = z₁ * z₂ ∧ z₂ ∈ integralImage F v ∧
      ∀ k : GL (Fin 2) (v.adicCompletion F), z₁ * embedAt F v k = embedAt F v k * z₁ :=
  ⟨stripAt F v z, embedAt F v (componentAt F v z), (stripAt_mul_embedAt F v z).symm, ⟨_, hz, rfl⟩,
    stripAt_commute F v z⟩

private theorem componentAt_mem_integralSubgroup_of_ne_zero {U : Subgroup (AdelicGL2 (𝓞 F) F)}
    {S : Finset (HeightOneSpectrum (𝓞 F))} {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsUnitFactorizableAt F U S f)
    (hv : v ∉ S) {z : AdelicGL2 (𝓞 F) F} (hz : f z ≠ 0) :
    componentAt F v z ∈ integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F) := by
  obtain ⟨-, fa, ff, fS, -, -, -, -, hoff, hfg⟩ := hf
  by_contra hcon
  apply hz
  have hnot : finComponent (𝓞 F) F v (glFin (𝓞 F) F z) ∉ localIntegralSet F v := fun hmem =>
    hcon (mem_integralSubgroup_of_mem_localIntegralSet F v hmem)
  rw [hfg z, hoff (glFin (𝓞 F) F z) ⟨v, hv, hnot⟩, mul_zero]

private def weylIntegral : GL (Fin 2) (v.adicCompletionIntegers F) :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

private def weylLocal : GL (Fin 2) (v.adicCompletion F) :=
  Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) (weylIntegral F v)

private theorem weylLocal_mem : weylLocal F v ∈ integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F) :=
  mem_integralSubgroup_iff.mpr ⟨weylIntegral F v, rfl⟩

private theorem coe_weylLocal : (weylLocal F v : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylLocal, weylIntegral, Matrix.GeneralLinearGroup.map]

private theorem componentAt_weyl : componentAt F v (weyl (𝓞 F) F) = weylLocal F v := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [coe_weylLocal]
  show ((((weyl (𝓞 F) F : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2) v
    = !![(0 : v.adicCompletion F), 1; 1, 0] i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem weyl_inv_mul_embedAt_mul_weyl (k : GL (Fin 2) (v.adicCompletion F)) :
    (weyl (𝓞 F) F)⁻¹ * embedAt F v k * weyl (𝓞 F) F = embedAt F v ((weylLocal F v)⁻¹ * k * weylLocal F v) := by
  have h1 : ∀ y : AdelicGL2 (𝓞 F) F, finComponent (𝓞 F) F v (glFin (𝓞 F) F y) = componentAt F v y := fun _ => rfl
  apply ext_of_components F
  · simp only [map_mul, map_inv, glArch_embedAt, inv_one, mul_one, inv_mul_cancel]
  · intro w
    by_cases hw : w = v
    · rw [hw]
      simp only [h1, map_mul, map_inv, componentAt_embedAt, componentAt_weyl]
    · simp only [map_mul, map_inv, finComponent_glFin_embedAt_of_ne F v (hw := hw), inv_one, mul_one,
        inv_mul_cancel]

private theorem integralImage_le_principalLevel_inf {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N) :
    integralImage F v ≤ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  rintro _ ⟨k, hk, rfl⟩
  have hlev : embedAt F v k ∈ levelGroup F N := integralImage_le_levelGroup F v hv ⟨k, hk, rfl⟩
  have hk' : (weylLocal F v)⁻¹ * k * weylLocal F v
      ∈ integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F) :=
    mul_mem (mul_mem (inv_mem (weylLocal_mem F v)) hk) (weylLocal_mem F v)
  have hconj : embedAt F v ((weylLocal F v)⁻¹ * k * weylLocal F v) ∈ levelOne (𝓞 F) F N :=
    (integralImage_le_levelGroup F v hv ⟨_, hk', rfl⟩).1
  refine ⟨⟨hlev.1, ?_⟩, hlev.2⟩
  refine Subgroup.mem_map.mpr ⟨(weyl (𝓞 F) F)⁻¹ * embedAt F v k * weyl (𝓞 F) F, ?_, ?_⟩
  · rw [weyl_inv_mul_embedAt_mul_weyl]
    exact hconj
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

end PrincipalCongruence
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end PrincipalCongruence
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

section PrincipalComponents

set_option autoImplicit false

p2m_open "NumberField IsDedekindDomain AutomorphicForm~continuous_unipotentGL2 P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm AdelicDock NumberField.AdelicLevel P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.CosetSystemLevel P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.PrincipalCongruence P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.LocalCongruence"

noncomputable section

namespace PrincipalComponents

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private theorem lower_of_isLevelOneMatrix {N : Ideal (𝓞 F)} {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)}
    (hm : IsLevelOneMatrix (𝓞 F) F N m) :
    (m 1 0) v ∈ localBall F v N ∧ (m 1 1) v - 1 ∈ localBall F v N := by
  refine ⟨hm.lowerLeft v, ?_⟩
  rw [mem_localBall]
  have h := hm.lowerRight v
  rwa [coe_sub_apply, coe_one_apply] at h

private theorem coe_componentAt_apply (x : AdelicGL2 (𝓞 F) F) (i j : Fin 2) :
    ((componentAt F v x : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j =
      ((glFin (𝓞 F) F x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))
        i j v :=
  rfl

private theorem componentAt_lower_of_mem_levelOne {N : Ideal (𝓞 F)} {x : AdelicGL2 (𝓞 F) F}
    (hx : x ∈ levelOne (𝓞 F) F N) :
    ((componentAt F v x : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0
        - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ∈ localBall F v N ∧
      ((componentAt F v x : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1
        - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 ∈ localBall F v N := by
  have hx' : glFin (𝓞 F) F x ∈ finiteLevelOne (𝓞 F) F N := hx
  obtain ⟨h10, h11⟩ := lower_of_isLevelOneMatrix F v hx'.1
  refine ⟨?_, ?_⟩
  · rw [coe_componentAt_apply, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero]
    exact h10
  · rw [coe_componentAt_apply, Matrix.one_apply_eq]
    exact h11

private theorem coe_weylLocal_inv :
    (((weylLocal F v)⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) =
      !![0, 1; 1, 0] := by
  rw [weylLocal, ← map_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylIntegral, Matrix.GeneralLinearGroup.map]

private theorem coe_weylLocal_inv_mul_mul_weylLocal (c : GL (Fin 2) (v.adicCompletion F)) (i j : Fin 2) :
    (((weylLocal F v)⁻¹ * c * weylLocal F v : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j =
      (c : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) (1 - i) (1 - j) := by
  rw [Units.val_mul, Units.val_mul, coe_weylLocal_inv, coe_weylLocal]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

private theorem coe_componentAt_mem_congruentMatrices_of_mem_principalLevel {N : Ideal (𝓞 F)} {x : AdelicGL2 (𝓞 F) F}
    (hx : x ∈ principalLevel (𝓞 F) F N) :
    ((componentAt F v x : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      ∈ congruentMatrices F v N := by
  obtain ⟨h10, h11⟩ := componentAt_lower_of_mem_levelOne F v hx.1
  obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx.2
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxy
  have hy' : y = (weyl (𝓞 F) F)⁻¹ * x * weyl (𝓞 F) F := by
    rw [← hxy]
    group
  have hc : componentAt F v y = (weylLocal F v)⁻¹ * componentAt F v x * weylLocal F v := by
    rw [hy', map_mul, map_mul, map_inv, componentAt_weyl]
  obtain ⟨h01, h00⟩ := componentAt_lower_of_mem_levelOne F v hy
  rw [hc, coe_weylLocal_inv_mul_mul_weylLocal] at h01 h00
  simp only [sub_self, sub_zero] at h01 h00
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using h00
  · simpa using h01
  · simpa using h10
  · simpa using h11

private theorem componentAt_mem_congruenceSet_of_mem_principalLevel {N : Ideal (𝓞 F)} {x : AdelicGL2 (𝓞 F) F}
    (hx : x ∈ principalLevel (𝓞 F) F N) : componentAt F v x ∈ congruenceSet F v N := by
  rw [mem_congruenceSet, ← map_inv]
  exact ⟨coe_componentAt_mem_congruentMatrices_of_mem_principalLevel F v hx,
    coe_componentAt_mem_congruentMatrices_of_mem_principalLevel F v (inv_mem hx)⟩

end PrincipalComponents
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end PrincipalComponents
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

section CongruenceTestFunction

set_option autoImplicit false

p2m_open "NumberField IsDedekindDomain AutomorphicForm~continuous_unipotentGL2 P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm NumberField.AdelicLevel P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.CosetSystemLevel P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.LocalCongruence P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.PrincipalComponents"

noncomputable section

namespace CongruenceTestFunction

variable (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (N : Ideal (𝓞 F))

private def finFactor (b : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : ℂ :=
  (unitFinSet F).indicator (fun _ => (1 : ℂ)) b *
    ∏ v ∈ S, (congruenceSet F v N).indicator (fun _ => (1 : ℂ)) (finComponent (𝓞 F) F v b)

private def finSet : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
  unitFinSet F ∩ ⋂ v ∈ S, finComponent (𝓞 F) F v ⁻¹' congruenceSet F v N

variable {F S N}

private theorem mem_finSet {b : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)} :
    b ∈ finSet F S N ↔ b ∈ unitFinSet F ∧ ∀ v ∈ S, finComponent (𝓞 F) F v b ∈ congruenceSet F v N := by
  simp only [finSet, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]

private theorem finFactor_eq_indicator : finFactor F S N = (finSet F S N).indicator fun _ => (1 : ℂ) := by
  classical
  ext b
  by_cases hb : b ∈ unitFinSet F
  · by_cases hS : ∀ v ∈ S, finComponent (𝓞 F) F v b ∈ congruenceSet F v N
    · rw [finFactor, Set.indicator_of_mem hb, one_mul, Set.indicator_of_mem (mem_finSet.mpr ⟨hb, hS⟩)]
      exact Finset.prod_eq_one fun v hv => Set.indicator_of_mem (hS v hv) _
    · obtain ⟨v, hv⟩ := not_forall.mp hS
      obtain ⟨hvS, hvc⟩ := Classical.not_imp.mp hv
      rw [finFactor, Set.indicator_of_notMem (fun h => hS (mem_finSet.mp h).2),
        Finset.prod_eq_zero hvS (Set.indicator_of_notMem hvc _), mul_zero]
  · rw [finFactor, Set.indicator_of_notMem hb, zero_mul, Set.indicator_of_notMem (fun h => hb (mem_finSet.mp h).1)]

private theorem finFactor_eq_zero_or_one (b : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    finFactor F S N b = 0 ∨ finFactor F S N b = 1 := by
  rw [finFactor_eq_indicator]
  by_cases hb : b ∈ finSet F S N
  · exact Or.inr (Set.indicator_of_mem hb _)
  · exact Or.inl (Set.indicator_of_notMem hb _)

private theorem finFactor_one : finFactor F S N 1 = 1 := by
  rw [finFactor_eq_indicator, Set.indicator_of_mem]
  refine mem_finSet.mpr ⟨one_mem_unitFinSet F, fun v _ => ?_⟩
  rw [map_one]
  exact one_mem_congruenceSet F v N

private
theorem mem_finSet_of_finFactor_ne_zero {b : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)} (hb : finFactor F S N b ≠ 0) :
    b ∈ finSet F S N := by
  by_contra h
  rw [finFactor_eq_indicator, Set.indicator_of_notMem h] at hb
  exact hb rfl

private theorem isFinTestFactor_finFactor (hN : N ≠ ⊥) : IsFinTestFactor F (finFactor F S N) := by
  have hopen : IsOpen (finSet F S N) :=
    (isOpen_unitFinSet F).inter (isOpen_biInter_finset fun v _ =>
      (isOpen_congruenceSet F v hN).preimage (continuous_finComponent (𝓞 F) F v))
  have hclosed : IsClosed (finSet F S N) :=
    (isCompact_unitFinSet F).isClosed.inter (isClosed_iInter fun v => isClosed_iInter fun _ =>
      (isClosed_congruenceSet F v N).preimage (continuous_finComponent (𝓞 F) F v))
  rw [finFactor_eq_indicator]
  refine ⟨isLocallyConstant_indicator_one hopen hclosed, HasCompactSupport.intro
    ((isCompact_unitFinSet F).of_isClosed_subset hclosed Set.inter_subset_left) fun b hb => ?_⟩
  exact Set.indicator_of_notMem hb _

private theorem finFactor_glFin_mul {x : AdelicGL2 (𝓞 F) F} (hx : ∀ v, componentAt F v x ∈ congruenceSet F v N)
    (b : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : finFactor F S N (glFin (𝓞 F) F x * b) = finFactor F S N b := by
  have hu : glFin (𝓞 F) F x ∈ finiteIntegralGL2 (𝓞 F) F := by
    have h : glFin (𝓞 F) F x ∈ unitFinSet F := fun v => by
      have h' := congruenceSet_subset_localIntegralSet F v N (hx v)
      simpa only [componentAt, MonoidHom.comp_apply] using h'
    rwa [unitFinSet_eq_finiteIntegralGL2, SetLike.mem_coe] at h
  unfold finFactor
  rw [indicator_unitFinSet_mul_left F hu]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  have hv : finComponent (𝓞 F) F v (glFin (𝓞 F) F x) ∈ congruenceSet F v N := by
    have h' := hx v
    simpa only [componentAt, MonoidHom.comp_apply] using h'
  rw [map_mul, indicator_congruenceSet_mul_left hv]

variable (F S N)

private theorem exists_isUnitFactorizableAt (hN : N ≠ ⊥) (Varch : Set (GL (Fin 2) (InfiniteAdeleRing F)))
    (hV : Varch ∈ nhds (1 : GL (Fin 2) (InfiniteAdeleRing F))) :
    ∃ f : AdelicGL2 (𝓞 F) F → ℂ,
      IsUnitFactorizableAt F ⊥ S f ∧
      (∀ x ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F, ∀ g, f (x * g) = f g) ∧
      (∀ g, (((f g).re : ℝ) : ℂ) = f g ∧ 0 ≤ (f g).re) ∧
      0 < (f 1).re ∧
      ∀ g, f g ≠ 0 → glArch (𝓞 F) F g ∈ Varch ∧ glFin (𝓞 F) F g ∈ unitFinSet F ∧
        ∀ v ∈ S, componentAt F v g ∈ congruenceSet F v N := by
  obtain ⟨fa, hfa, hreal, hpos, hsupp, -, -⟩ :=
    exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat F 0 Varch hV
  refine ⟨fun g => fa (glArch (𝓞 F) F g) * finFactor F S N (glFin (𝓞 F) F g), ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨isBiInvariantUnder_bot F _, fa, finFactor F S N,
      fun v => (congruenceSet F v N).indicator fun _ => (1 : ℂ), hfa, isFinTestFactor_finFactor hN,
      fun v _ => isLocalTestFn_indicator_congruenceSet F v N hN, fun b hb => ?_, fun b hb => ?_, fun _ => rfl⟩
    · by_cases hu : b ∈ unitFinSet F
      · simp only [finFactor, Set.indicator_of_mem hu, one_mul]
      · obtain ⟨v, hv⟩ := not_forall.mp hu
        have hvS : v ∈ S := by
          by_contra hvS
          exact hv (hb v hvS)
        have hvc : finComponent (𝓞 F) F v b ∉ congruenceSet F v N := fun h =>
          hv (congruenceSet_subset_localIntegralSet F v N h)
        rw [finFactor, Set.indicator_of_notMem hu, zero_mul]
        exact (Finset.prod_eq_zero hvS (Set.indicator_of_notMem hvc _)).symm
    · obtain ⟨v, -, hv⟩ := hb
      have hu : b ∉ unitFinSet F := fun h => hv (h v)
      rw [finFactor, Set.indicator_of_notMem hu, zero_mul]
  · intro x hx g
    have ha : glArch (𝓞 F) F x = 1 := (mem_finiteAdelicGL2Subgroup_iff F x).mp hx.2
    show fa (glArch (𝓞 F) F (x * g)) * finFactor F S N (glFin (𝓞 F) F (x * g)) =
      fa (glArch (𝓞 F) F g) * finFactor F S N (glFin (𝓞 F) F g)
    rw [map_mul, map_mul, ha, one_mul,
      finFactor_glFin_mul (fun v => componentAt_mem_congruenceSet_of_mem_principalLevel F v hx.1)]
  · intro g
    obtain h | h := finFactor_eq_zero_or_one (F := F) (S := S) (N := N) (glFin (𝓞 F) F g)
    · simp only [h, mul_zero, Complex.zero_re, Complex.ofReal_zero, le_refl, and_self]
    · simp only [h, mul_one]
      exact hreal _
  · show 0 < (fa (glArch (𝓞 F) F 1) * finFactor F S N (glFin (𝓞 F) F 1)).re
    rw [map_one, map_one, finFactor_one, mul_one]
    exact hpos
  · intro g hg
    have hg' : fa (glArch (𝓞 F) F g) * finFactor F S N (glFin (𝓞 F) F g) ≠ 0 := hg
    have h1 : fa (glArch (𝓞 F) F g) ≠ 0 := left_ne_zero_of_mul hg'
    have h2 := mem_finSet.mp (mem_finSet_of_finFactor_ne_zero (right_ne_zero_of_mul hg'))
    refine ⟨hsupp (subset_tsupport _ h1), h2.1, fun v hv => ?_⟩
    simp only [componentAt, MonoidHom.comp_apply]
    exact h2.2 v hv

end CongruenceTestFunction
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end CongruenceTestFunction
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

section LevelIdeal

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace LevelIdeal

variable {F : Type} [Field F] [NumberField F]

private def levelIdeal (T : Finset (HeightOneSpectrum (𝓞 F))) (n : HeightOneSpectrum (𝓞 F) → ℕ) : Ideal (𝓞 F) :=
  ∏ v ∈ T, v.asIdeal ^ n v

omit [NumberField F] in
private theorem levelIdeal_ne_bot (T : Finset (HeightOneSpectrum (𝓞 F))) (n : HeightOneSpectrum (𝓞 F) → ℕ) :
    levelIdeal T n ≠ ⊥ := by
  unfold levelIdeal
  rw [← Ideal.zero_eq_bot]
  exact Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)

omit [NumberField F] in
private theorem pow_dvd_levelIdeal {T : Finset (HeightOneSpectrum (𝓞 F))} (n : HeightOneSpectrum (𝓞 F) → ℕ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ T) : v.asIdeal ^ n v ∣ levelIdeal T n :=
  Finset.dvd_prod_of_mem (fun w => w.asIdeal ^ n w) hv

private theorem mem_of_asIdeal_dvd_levelIdeal {T : Finset (HeightOneSpectrum (𝓞 F))} {n : HeightOneSpectrum (𝓞 F) → ℕ}
    {w : HeightOneSpectrum (𝓞 F)} (hw : w.asIdeal ∣ levelIdeal T n) : w ∈ T := by
  have hw' : w.asIdeal ∣ ∏ v ∈ T, v.asIdeal ^ n v := hw
  obtain ⟨v, hvT, hwv⟩ := (w.prime.dvd_finsetProd_iff _).1 hw'
  have hwv' : w.asIdeal = v.asIdeal :=
    associated_iff_eq.1 (w.prime.associated_of_dvd v.prime (w.prime.dvd_of_dvd_pow hwv))
  rwa [HeightOneSpectrum.ext hwv']

private theorem exists_ne_bot_forall_dvd_mem_forall_pow_dvd {T S : Finset (HeightOneSpectrum (𝓞 F))} (hTS : T ⊆ S)
    (n : HeightOneSpectrum (𝓞 F) → ℕ) :
    ∃ N : Ideal (𝓞 F), N ≠ ⊥ ∧ (∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ N → v ∈ S) ∧
      ∀ v ∈ T, v.asIdeal ^ n v ∣ N :=
  ⟨levelIdeal T n, levelIdeal_ne_bot T n, fun _ hv => hTS (mem_of_asIdeal_dvd_levelIdeal hv),
    fun _ hv => pow_dvd_levelIdeal n hv⟩

end LevelIdeal
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end LevelIdeal
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

section SmoothingNonvanishing

set_option autoImplicit false

p2m_open "NumberField IsDedekindDomain AutomorphicForm~continuous_unipotentGL2 P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm NumberField.AdelicLevel NumberField.AdelicHaar P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.CosetSystemLevel P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.PrincipalCongruence MeasureTheory Topology"

noncomputable section

namespace SmoothingNonvanishing

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

variable (F : Type) [Field F] [NumberField F]

private theorem glArch_stripAt (v : HeightOneSpectrum (𝓞 F)) (y : AdelicGL2 (𝓞 F) F) :
    glArch (𝓞 F) F (stripAt F v y) = glArch (𝓞 F) F y := by
  rw [stripAt, map_mul, map_inv, glArch_embedAt, inv_one, mul_one]

private theorem componentAt_stripAt_of_ne (v : HeightOneSpectrum (𝓞 F)) (y : AdelicGL2 (𝓞 F) F)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) : componentAt F w (stripAt F v y) = componentAt F w y := by
  have h1 : componentAt F w (embedAt F v (componentAt F v y)) = 1 := by
    simp only [componentAt, MonoidHom.comp_apply]
    exact finComponent_glFin_embedAt_of_ne F v _ hw
  rw [stripAt, map_mul, map_inv, h1, inv_one, mul_one]

private def IsSphericalOff (S₁ : Finset (HeightOneSpectrum (𝓞 F))) (h : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S₁ → ∀ g : AdelicGL2 (𝓞 F) F,
    ∀ k ∈ (LocalGL2.integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F)).map
      ((AdelicDock.finEmbed (𝓞 F) F).comp (AdelicDock.localEmbed (𝓞 F) F v)), h (g * k) = h g

variable {F}

private theorem IsSphericalOff.mul_embedAt {S₁ : Finset (HeightOneSpectrum (𝓞 F))} {h : AdelicGL2 (𝓞 F) F → ℂ}
    (hsph : IsSphericalOff F S₁ h) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S₁) (g : AdelicGL2 (𝓞 F) F)
    {k : GL (Fin 2) (v.adicCompletion F)} (hk : k ∈ localIntegralSet F v) : h (g * embedAt F v k) = h g :=
  hsph v hv g _ (Subgroup.mem_map.mpr ⟨k, mem_integralSubgroup_of_mem_localIntegralSet F v hk, rfl⟩)

private theorem exists_strip {S₁ : Finset (HeightOneSpectrum (𝓞 F))} {h : AdelicGL2 (𝓞 F) F → ℂ}
    (hsph : IsSphericalOff F S₁ h) (g₀ : AdelicGL2 (𝓞 F) F) (E : Finset (HeightOneSpectrum (𝓞 F))) :
    (∀ v ∈ E, v ∉ S₁) → ∀ y : AdelicGL2 (𝓞 F) F, (∀ v ∈ E, componentAt F v y ∈ localIntegralSet F v) →
      ∃ y' : AdelicGL2 (𝓞 F) F, h (g₀ * y) = h (g₀ * y') ∧ glArch (𝓞 F) F y' = glArch (𝓞 F) F y ∧
        (∀ v ∈ E, componentAt F v y' = 1) ∧ ∀ w ∉ E, componentAt F w y' = componentAt F w y := by
  classical
  refine Finset.induction_on E (fun _ y _ => ⟨y, rfl, rfl, fun v hv => absurd hv (Finset.notMem_empty v),
    fun _ _ => rfl⟩) ?_
  intro a E ha ih hE y hy
  have haS : a ∉ S₁ := hE a (Finset.mem_insert_self a E)
  have hstep : h (g₀ * y) = h (g₀ * stripAt F a y) := by
    conv_lhs => rw [← stripAt_mul_embedAt F a y, ← mul_assoc]
    exact hsph.mul_embedAt haS _ (hy a (Finset.mem_insert_self a E))
  obtain ⟨y', h1, h2, h3, h4⟩ := ih (fun v hv => hE v (Finset.mem_insert_of_mem hv)) (stripAt F a y) fun v hv => by
    have hva : v ≠ a := fun hva => ha (hva ▸ hv)
    rw [componentAt_stripAt_of_ne F a y hva]
    exact hy v (Finset.mem_insert_of_mem hv)
  refine ⟨y', hstep.trans h1, h2.trans (glArch_stripAt F a y), fun v hv => ?_, fun w hw => ?_⟩
  · rcases Finset.mem_insert.mp hv with rfl | hv
    · rw [h4 v ha, componentAt_stripAt]
    · exact h3 v hv
  · have hwa : w ≠ a := fun hwa => hw (hwa ▸ Finset.mem_insert_self a E)
    have hwE : w ∉ E := fun hwE => hw (Finset.mem_insert_of_mem hwE)
    rw [h4 w hwE, componentAt_stripAt_of_ne F a y hwa]

private theorem rightConv_ne_zero_of_forall_norm_sub_lt {h f : AdelicGL2 (𝓞 F) F → ℂ} (hcont : Continuous h)
    (hfc : Continuous f) (hfs : HasCompactSupport f) (hfreal : ∀ x, (((f x).re : ℝ) : ℂ) = f x ∧ 0 ≤ (f x).re)
    (hfpos : 0 < (f 1).re) {g₀ : AdelicGL2 (𝓞 F) F} (hg₀ : h g₀ ≠ 0)
    (hest : ∀ x, f x ≠ 0 → ‖h (g₀ * x) - h g₀‖ < ‖h g₀‖ / 2) : rightConv F h f g₀ ≠ 0 := by
  set μ := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  set fr : AdelicGL2 (𝓞 F) F → ℝ := fun x => (f x).re with hfr
  have hf_eq : f = fun x => ((fr x : ℝ) : ℂ) := funext fun x => ((hfreal x).1).symm
  have hfr_cont : Continuous fr := Complex.continuous_re.comp hfc
  have hfr_supp : HasCompactSupport fr := hfs.comp_left Complex.zero_re
  have hfr_int : Integrable fr μ := hfr_cont.integrable_of_hasCompactSupport hfr_supp
  have hfr_nonneg : ∀ x, 0 ≤ fr x := fun x => (hfreal x).2

  have hc : 0 < ∫ x, fr x ∂μ := by
    rw [integral_pos_iff_support_of_nonneg hfr_nonneg hfr_int]
    exact hfr_cont.isOpen_support.measure_pos μ ⟨1, hfpos.ne'⟩
  set c : ℝ := ∫ x, fr x ∂μ with hcdef
  have hf_int : Integrable f μ := hfc.integrable_of_hasCompactSupport hfs
  have hφ : Continuous fun x => h (g₀ * x) := hcont.comp (continuous_const_mul g₀)
  have hφf_int : Integrable (fun x => h (g₀ * x) * f x) μ :=
    (hφ.mul hfc).integrable_of_hasCompactSupport hfs.mul_left
  have hint_f : ∫ x, f x ∂μ = (c : ℂ) := by
    rw [hf_eq, integral_complex_ofReal]

  have hdiff : rightConv F h f g₀ - h g₀ * c = ∫ x, (h (g₀ * x) - h g₀) * f x ∂μ := by
    have hR : rightConv F h f g₀ = ∫ x, h (g₀ * x) * f x ∂μ := rfl
    rw [hR, ← hint_f, ← integral_const_mul, ← integral_sub hφf_int (hf_int.const_mul _)]
    simp only [sub_mul]

  have hbound : ∀ x, ‖(h (g₀ * x) - h g₀) * f x‖ ≤ ‖h g₀‖ / 2 * fr x := by
    intro x
    rw [norm_mul, show f x = ((fr x : ℝ) : ℂ) from ((hfreal x).1).symm, Complex.norm_of_nonneg (hfr_nonneg x)]
    by_cases hx : f x = 0
    · have h0 : fr x = 0 := by
        simp only [hfr, hx, Complex.zero_re]
      rw [h0, mul_zero, mul_zero]
    · exact mul_le_mul_of_nonneg_right (hest x hx).le (hfr_nonneg x)
  have hnorm : ‖rightConv F h f g₀ - h g₀ * c‖ ≤ ‖h g₀‖ / 2 * c := by
    rw [hdiff, hcdef, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (hfr_int.const_mul _) (Filter.Eventually.of_forall hbound)
  intro hzero
  rw [hzero, zero_sub, norm_neg, norm_mul, Complex.norm_of_nonneg hc.le] at hnorm
  have hpos : 0 < ‖h g₀‖ := norm_pos_iff.mpr hg₀
  nlinarith [hnorm, mul_pos hpos hc]

variable (F)

private theorem exists_level_exists_isUnitFactorizableAt_rightConv_ne_zero (S₁ : Finset (HeightOneSpectrum (𝓞 F)))
    {h : AdelicGL2 (𝓞 F) F → ℂ} (hcont : Continuous h) (hsph : IsSphericalOff F S₁ h) {g₀ : AdelicGL2 (𝓞 F) F}
    (hg₀ : h g₀ ≠ 0) :
    ∃ N : Ideal (𝓞 F), N ≠ ⊥ ∧ (∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ N → v ∈ S₁) ∧
      ∃ f : AdelicGL2 (𝓞 F) F → ℂ, IsUnitFactorizableAt F ⊥ S₁ f ∧
        (∀ x ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F, ∀ g, f (x * g) = f g) ∧
        (∀ z, f z ≠ 0 → glFin (𝓞 F) F z ∈ unitFinSet F) ∧ rightConv F h f g₀ ≠ 0 := by
  classical

  have hε : 0 < ‖h g₀‖ / 2 := by
    have := norm_pos_iff.mpr hg₀
    positivity
  have hφ : Continuous fun y : AdelicGL2 (𝓞 F) F => h (g₀ * y) := hcont.comp (continuous_const_mul g₀)
  have hV : (fun y : AdelicGL2 (𝓞 F) F => h (g₀ * y)) ⁻¹' Metric.ball (h (g₀ * 1)) (‖h g₀‖ / 2) ∈ 𝓝 1 :=
    hφ.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
  obtain ⟨Varch, hVarch, T, W, hW, hVmem⟩ := AdelicNeighbourhood.exists_nhds_one_unpacking F _ hV

  choose n hn using fun v => CongruenceBasis.exists_nat_congruenceSet_subset F v (hW v)
  obtain ⟨N, hN, hNS, hpow⟩ :=
    LevelIdeal.exists_ne_bot_forall_dvd_mem_forall_pow_dvd (Finset.inter_subset_right : T ∩ S₁ ⊆ S₁) n
  obtain ⟨f, hf, hfinv, hfreal, hfpos, hfsupp⟩ :=
    CongruenceTestFunction.exists_isUnitFactorizableAt F S₁ N hN Varch hVarch
  obtain ⟨hfc, hfs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf.isFactorizableTestFn
  refine ⟨N, hN, hNS, f, hf, hfinv, fun z hz => (hfsupp z hz).2.1, ?_⟩
  refine rightConv_ne_zero_of_forall_norm_sub_lt hcont hfc hfs hfreal hfpos hg₀ fun y hy => ?_
  obtain ⟨hyarch, hyunit, hycong⟩ := hfsupp y hy
  have hyint : ∀ v, componentAt F v y ∈ localIntegralSet F v := fun v => by
    simp only [componentAt, MonoidHom.comp_apply]
    exact hyunit v

  obtain ⟨y', hy', harch, hone, hsame⟩ := exists_strip hsph g₀ (T \ S₁) (fun v hv => (Finset.mem_sdiff.mp hv).2) y
    fun v _ => hyint v
  have hmem : y' ∈ (fun z : AdelicGL2 (𝓞 F) F => h (g₀ * z)) ⁻¹' Metric.ball (h (g₀ * 1)) (‖h g₀‖ / 2) := by
    refine hVmem y' (harch ▸ hyarch) (fun v hvT => ?_) fun w hwT => ?_
    · show componentAt F v y' ∈ W v
      by_cases hvS : v ∈ S₁
      · have hvE : v ∉ T \ S₁ := fun hvE => (Finset.mem_sdiff.mp hvE).2 hvS
        rw [hsame v hvE]
        have hdvd := hpow v (Finset.mem_inter.mpr ⟨hvT, hvS⟩)
        exact hn v N (CongruenceBasis.idealBound_le_exp_neg_of_pow_dvd F v hN hdvd) (hycong v hvS)
      · rw [hone v (Finset.mem_sdiff.mpr ⟨hvT, hvS⟩)]
        exact mem_of_mem_nhds (hW v)
    · show componentAt F w y' ∈ localIntegralSet F w
      have hwE : w ∉ T \ S₁ := fun hwE => hwT (Finset.mem_sdiff.mp hwE).1
      rw [hsame w hwE]
      exact hyint w
  have hball := Metric.mem_ball.mp hmem
  rw [dist_eq_norm, mul_one] at hball
  rwa [hy']

end SmoothingNonvanishing
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end SmoothingNonvanishing
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

section IsotypicLiteral

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
p2m_open "AutomorphicForm~continuous_unipotentGL2 P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp"
open NumberField.AdelicHaar MeasureTheory

noncomputable section

namespace IsotypicLiteral

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

private theorem rightConv_mul_right_eq_of_forall (h f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) {x : AdelicGL2 (𝓞 ℚ) ℚ}
    (hx : ∀ z, f (x⁻¹ * z) = f z) (g : AdelicGL2 (𝓞 ℚ) ℚ) : rightConv ℚ h f (g * x) = rightConv ℚ h f g := by
  show (∫ z, h (g * x * z) * f z ∂adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) = ∫ z, h (g * z) * f z ∂adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
  have key := integral_mul_left_eq_self (μ := adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) (fun z => h (g * z) * f (x⁻¹ * z)) x
  simp only [← mul_assoc, inv_mul_cancel, one_mul] at key
  rw [key]
  simp only [hx]

private theorem exists_isIsotypicCuspFormAt_principalLevel_ne_zero
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (a b : HeightOneSpectrum (𝓞 ℚ) → ℂ) (S₁ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (h : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hcont : Continuous h)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      h (globalPoints (𝓞 ℚ) ℚ γ * g) = h g)
    (hcentral : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      h (centralScalar (𝓞 ℚ) ℚ z * g) = ((ξ z : ℂˣ) : ℂ) * h g)
    (hcusp : @IsCuspidalFn _
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).nS
      _ _
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).ν
      unipotentGL2 h)
    (hgrowth : ∀ c' u' d₁' d₂' : ℝ, 0 < c' → 0 < d₁' →
      IsSlowlyIncreasingOn (centreCutSiegelSet ℚ c' u' d₁' d₂') (NumberField.AdelicHeight.adelicHeight ℚ) h)
    (hsph : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S₁ → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      ∀ k ∈ (LocalGL2.integralSubgroup (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)).map
        ((AdelicDock.finEmbed (𝓞 ℚ) ℚ).comp (AdelicDock.localEmbed (𝓞 ℚ) ℚ v)), h (g * k) = h g)
    (hhecke : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S₁ →
      IsHeckeCosetEigenfunctionAt ℚ
        ((LocalGL2.integralSubgroup (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)).map
          ((AdelicDock.finEmbed (𝓞 ℚ) ℚ).comp (AdelicDock.localEmbed (𝓞 ℚ) ℚ v)))
        (heckeGen (𝓞 ℚ) ℚ v) v h (a v))
    (hcentre : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S₁ → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      h (centralScalar (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 ℚ) ℚ v)) * g)
        = (HeckeEigensystem.cNorm v)⁻¹ * b v * h g)
    (hne : ∃ g : AdelicGL2 (𝓞 ℚ) ℚ, h g ≠ 0) :
    ∃ (N' : Ideal (𝓞 ℚ)) (hN' : N' ≠ ⊥), (∀ v : HeightOneSpectrum (𝓞 ℚ), v.asIdeal ∣ N' → v ∈ S₁) ∧
      ∃ φ₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ,
        IsIsotypicCuspFormAt ℚ
          (productionPinsOf ℚ (PrincipalToLevelOne.enlargedWindow c u d₁ d₂ T)
            (fun N => principalLevel (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
            (adelicBox ℚ))
          (ξ.comp (productionPinsOf ℚ (PrincipalToLevelOne.enlargedWindow c u d₁ d₂ T)
            (fun N => principalLevel (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
            (adelicBox ℚ)).Z.subtype)
          N' S₁ ⟨N', hN', a, b⟩ φ₁ ∧ φ₁ ≠ 0 := by
  obtain ⟨g₀, hg₀⟩ := hne
  obtain ⟨N', hN', hN'S, f, hf, hfinv, -, hconv⟩ :=
    SmoothingNonvanishing.exists_level_exists_isUnitFactorizableAt_rightConv_ne_zero ℚ S₁ hcont hsph hg₀
  have hff : IsFactorizableTestFn ℚ f := hf.isFactorizableTestFn
  obtain ⟨hfc, hfs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn ℚ f hff
  refine ⟨N', hN', hN'S, rightConv ℚ h f, ?_, fun h0 => hconv (congrFun h0 g₀)⟩
  refine
    { smoothCusp := ⟨⟨?_, ?_⟩, isKfSmooth_rightConv ℚ h f hff⟩
      continuous := (continuous_rightConv_and_contDiff_of_isFactorizableTestFn ℚ h hcont f hff).1
      level_invariant := fun g x hx => ?_
      hecke_eigen := fun v hv => ?_
      central_eigen := fun v hv g => ?_ }
  ·
    refine (lsXiMemberAt_iff (𝓞 ℚ) ℚ _ _ _ _ _).mpr ⟨⟨fun γ g => ?_, fun z g => ?_⟩, ?_⟩
    · exact HeckeThroughConv.rightConv_mul_left_eq_of_forall h f _ (hleft γ) g
    · exact HeckeThroughConv.rightConv_mul_left_eq_mul_of_forall h f _ _ (hcentral z) g
    · exact GodementEstimate.memLp_two_rightConv_restrict h ξ hcont hleft hcentral hcusp hgrowth f hff _ _ d₁ d₂ _
        (lt_min hc (by positivity)) hd₁
  ·
    exact isCuspidalFn_rightConv ℚ _ _ _ h hcont hcusp f hff
  ·
    exact rightConv_mul_right_eq_of_forall h f (fun z => hfinv _ (inv_mem hx) z) g
  ·
    have hvN : ¬ v.asIdeal ∣ N' := fun hdvd => hv (hN'S v hdvd)
    have hsupp : ∀ z : AdelicGL2 (𝓞 ℚ) ℚ, f z ≠ 0 → ∃ z₁ z₂ : AdelicGL2 (𝓞 ℚ) ℚ,
        z = z₁ * z₂ ∧ z₂ ∈ HeckeThroughConv.sphericalImage v ∧
          ∀ xv : GL (Fin 2) (v.adicCompletion ℚ),
            z₁ * UnramifiedWhittaker.placeEmbed ℚ v xv = UnramifiedWhittaker.placeEmbed ℚ v xv * z₁ := by
      intro z hz
      obtain ⟨z₁, z₂, hz12, hz₂, hcomm⟩ := PrincipalCongruence.exists_eq_mul_of_componentAt_mem ℚ v
        (PrincipalCongruence.componentAt_mem_integralSubgroup_of_ne_zero ℚ v hf hv hz)
      exact ⟨z₁, z₂, hz12, hz₂, hcomm⟩
    have hint : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        Integrable (fun z => h (g * z) * f z) (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := fun g =>
      ((hcont.comp (continuous_const_mul g)).mul hfc).integrable_of_hasCompactSupport hfs.mul_left
    have hH := HeckeThroughConv.isHeckeCosetEigenfunctionAt_rightConv v h f (a v) (hsph v hv) (hhecke v hv) hsupp hint
    exact IntermediateLevel.isHeckeCosetEigenfunctionAt_principalLevel ℚ v
      (PrincipalCongruence.integralImage_le_principalLevel_inf ℚ v hvN) hH
  ·
    exact HeckeThroughConv.rightConv_mul_left_eq_mul_of_forall h f _ _ (hcentre v hv) g

end IsotypicLiteral
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

end IsotypicLiteral
p2m_reactivate "P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.UnipotentAverage P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm.GodementEstimate"

open NumberField NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
p2m_open "AutomorphicForm~continuous_unipotentGL2 P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp"

theorem solution
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (a b : HeightOneSpectrum (𝓞 ℚ) → ℂ) (S₁ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (h : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hcont : Continuous h)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      h (globalPoints (𝓞 ℚ) ℚ γ * g) = h g)
    (hcentral : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      h (centralScalar (𝓞 ℚ) ℚ z * g) = ((ξ z : ℂˣ) : ℂ) * h g)
    (hcusp : @IsCuspidalFn _
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).nS
      _ _
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).ν
      unipotentGL2 h)
    (hgrowth : ∀ c' u' d₁' d₂' : ℝ, 0 < c' → 0 < d₁' →
      IsSlowlyIncreasingOn (centreCutSiegelSet ℚ c' u' d₁' d₂') (NumberField.AdelicHeight.adelicHeight ℚ) h)
    (hsph : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S₁ → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      ∀ k ∈ (LocalGL2.integralSubgroup (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)).map
        ((AdelicDock.finEmbed (𝓞 ℚ) ℚ).comp (AdelicDock.localEmbed (𝓞 ℚ) ℚ v)), h (g * k) = h g)
    (hhecke : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S₁ →
      IsHeckeCosetEigenfunctionAt ℚ
        ((LocalGL2.integralSubgroup (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)).map
          ((AdelicDock.finEmbed (𝓞 ℚ) ℚ).comp (AdelicDock.localEmbed (𝓞 ℚ) ℚ v)))
        (heckeGen (𝓞 ℚ) ℚ v) v h (a v))
    (hcentre : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S₁ → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      h (centralScalar (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 ℚ) ℚ v)) * g)
        = (HeckeEigensystem.cNorm v)⁻¹ * b v * h g)
    (hne : ∃ g : AdelicGL2 (𝓞 ℚ) ℚ, h g ≠ 0) :
    ∃ (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥), (∀ v : HeightOneSpectrum (𝓞 ℚ), v.asIdeal ∣ N → v ∈ S₁) ∧
      IsArithGenuineCuspRealizable ℚ
        (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        ⟨N, hN, a, b⟩ := by
  obtain ⟨N', hN', hN'S, φ₁, hφ₁, hφ₁0⟩ :=
    IsotypicLiteral.exists_isIsotypicCuspFormAt_principalLevel_ne_zero c u d₁ d₂ T hc hd₁ a b S₁ ξ h hcont hleft
      hcentral hcusp hgrowth hsph hhecke hcentre hne
  exact PrincipalToLevelOne.exists_level_isArithGenuineCuspRealizable_of_isIsotypicCuspFormAt_principalLevel
    c u d₁ d₂ T hc hd₁ hd a b S₁ _ N' hN' hN'S φ₁ hφ₁ hφ₁0

#print axioms solution

end S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat
end P2MW
export P2MW.S_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat (solution)
