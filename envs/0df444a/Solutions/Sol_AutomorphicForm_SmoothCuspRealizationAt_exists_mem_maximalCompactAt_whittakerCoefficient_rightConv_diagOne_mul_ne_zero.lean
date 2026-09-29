-- Prove2me | solution 1 for AutomorphicForm.SmoothCuspRealizationAt.exists_mem_maximalCompactAt_whittakerCoefficient_rightConv_diagOne_mul_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/969d1b0a-5de4-5203-a178-e245d62fed79

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact

import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_unramified_package_rightConv_sum_translate
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Theorems.Thm_AutomorphicForm_hasSum_whittakerCoefficient_one_diagOne_principalIdeles_mul
import Theorems.Thm_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero
import Theorems.Thm_AutomorphicForm_exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_mem_maximalCompactAt_whittakerCoefficient_rightConv_diagOne_mul_ne_zero
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val"

set_option autoImplicit false

open NumberField NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp IsDedekindDomain

open MeasureTheory NumberField.AdelicHaar
open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

open HeckeIntegralSeam
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

theorem unipotentGL2_algebraMap_eq_globalPoints (K : Type) [Field K] [NumberField K] (β : K) :
    unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) = globalPoints (𝓞 K) K (unipotentGL2 β) := by
  refine Units.ext ?_
  ext i j
  simp only [unipotentGL2_coe, globalPoints, Matrix.GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply]
  fin_cases i <;> fin_cases j <;> simp

end RS12T

namespace RS27

variable (K : Type) [Field K] [NumberField K]

noncomputable abbrev W1 (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) : ℂ :=
  whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
    (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
    (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) φ 1 g

theorem gl_ext {g h : AdelicGL2 (𝓞 K) K} (h₁ : glArch (𝓞 K) K g = glArch (𝓞 K) K h)
    (h₂ : ∀ u, finComponent (𝓞 K) K u (glFin (𝓞 K) K g) = finComponent (𝓞 K) K u (glFin (𝓞 K) K h)) :
    g = h := by
  apply Units.ext
  ext i j
  apply Prod.ext
  · have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing K) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) h₁) i) j
    rwa [glArch_apply, glArch_apply] at this
  · refine RestrictedProduct.ext _ _ fun u => ?_
    have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (u.adicCompletion K) => (m : Matrix (Fin 2) (Fin 2) (u.adicCompletion K))) (h₂ u)) i) j
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

theorem snd_one_apply (v : HeightOneSpectrum (𝓞 K)) (i j : Fin 2) :
    evalAt K v ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) = (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

theorem snd_apply_diagOne_of_snd_eq_one (a : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K))
    (ha : ((a : AdeleRing (𝓞 K) K)).2 v = 1) (i j : Fin 2) :
    (((diagOne a : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v =
      ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v := by
  rw [evalAt_eq] at ha
  rw [diagOne_coe_apply, evalAt_eq, evalAt_eq, snd_one_apply]
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, ha]

theorem snd_apply_mul_of_trivial (g g' : AdelicGL2 (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K))
    (hg : ∀ i j : Fin 2, ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v =
      ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v)
    (hg' : ∀ i j : Fin 2, ((g' : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v =
      ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v) (i j : Fin 2) :
    (((g * g' : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v =
      ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v := by
  simp only [evalAt_eq, snd_one_apply] at hg hg' ⊢
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, map_mul, hg, hg, hg', hg']
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

theorem mem_levelOne_of_trivial_at (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S)
    (k : AdelicGL2 (𝓞 K) K) (hk : k ∈ levelOne (𝓞 K) K ⊤ ⊓ finiteAdelicGL2Subgroup K)
    (hkS : ∀ v ∈ S, ∀ i j : Fin 2, ((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v =
      ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v) :
    k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K := by
  rw [Subgroup.mem_inf] at hk ⊢
  refine ⟨?_, hk.2⟩
  have hk1 := hk.1
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at hk1 ⊢

  have hkS1 : ∀ v ∈ S, ∀ i j : Fin 2, evalAt K v ((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) =
      (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := by
    intro v hv i j; rw [← evalAt_eq, hkS v hv i j, evalAt_eq, snd_one_apply]

  have hkS' : ∀ v ∈ S, ∀ i j : Fin 2, evalAt K v (((k⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) =
      (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := by
    intro v hv

    have hmap : ∀ (m : AdelicGL2 (𝓞 K) K),
        ((evalAt K v).mapMatrix ((m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)))) *
          ((evalAt K v).mapMatrix (((m⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)))) = 1 := by
      intro m
      rw [← RingHom.map_mul]
      change (evalAt K v).mapMatrix (((m * m⁻¹ : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = 1
      rw [mul_inv_cancel, Units.val_one, map_one]
    have hk1m : (evalAt K v).mapMatrix ((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) = 1 := by
      ext i j; rw [RingHom.mapMatrix_apply, Matrix.map_apply]; exact hkS1 v hv i j
    have hinv := hmap k
    rw [hk1m, one_mul] at hinv
    intro i j
    have := congrFun (congrFun hinv i) j
    rwa [RingHom.mapMatrix_apply, Matrix.map_apply] at this
  have aux : ∀ m : AdelicGL2 (𝓞 K) K, IsLevelOneMatrix (𝓞 K) K ⊤ (glFin (𝓞 K) K m : Matrix _ _ _) →
      (∀ v ∈ S, ∀ i j : Fin 2, evalAt K v ((m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) =
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) →
      IsLevelOneMatrix (𝓞 K) K N (glFin (𝓞 K) K m : Matrix _ _ _) := by
    intro m hm hmS
    have hball : ∀ x : FiniteAdeleRing (𝓞 K) K, (∀ v, Valued.v (x v) ≤ 1) → (∀ v ∈ S, x v = 0) →
        x ∈ idealBall (𝓞 K) K N := by
      intro x hx hx0 v
      by_cases hvN : v.asIdeal ∣ N
      · rw [hx0 v (hS v hvN), map_zero]; exact zero_le'
      · rw [idealBound_eq_one_of_not_dvd hN hvN]; exact hx v
    have hint : ∀ (i j : Fin 2) (v : HeightOneSpectrum (𝓞 K)),
        Valued.v (((glFin (𝓞 K) K m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) v) ≤
          (1 : WithZero (Multiplicative ℤ)) := fun i j v =>
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hm.integral i j v)
    refine ⟨⟨hm.integral, hball _ (hint 1 0) fun v hv => ?_⟩, hball _ ?_ fun v hv => ?_⟩
    · have := hmS v hv 1 0
      rw [glFin_apply, evalAt_eq]; simpa [Matrix.one_apply] using this
    · intro v
      have e2 : ((glFin (𝓞 K) K m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 1 1 - 1) v =
          ((glFin (𝓞 K) K m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 1 1) v - 1 := by
        show finAdeleEval (𝓞 K) K v (((glFin (𝓞 K) K m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 1 1) - 1) =
          finAdeleEval (𝓞 K) K v ((glFin (𝓞 K) K m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 1 1) - 1
        rw [map_sub, map_one]
      rw [e2]
      have h1 := hint 1 1 v

      calc Valued.v (((glFin (𝓞 K) K m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 1 1) v - 1)
          ≤ max (Valued.v (((glFin (𝓞 K) K m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 1 1) v))
              (Valued.v (1 : v.adicCompletion K)) :=
            Valuation.map_sub _ _ _
        _ ≤ 1 := max_le h1 (by rw [map_one])
    · have := hmS v hv 1 1
      show finAdeleEval (𝓞 K) K v (((glFin (𝓞 K) K m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 1 1) - 1) = 0
      rw [map_sub, map_one, sub_eq_zero]
      rw [Matrix.one_apply_eq] at this
      exact this
  refine ⟨aux k hk1.1 hkS1, ?_⟩
  have := aux k⁻¹ (by rw [map_inv]; exact hk1.2) hkS'
  rwa [map_inv] at this

end RS27

end

set_option maxHeartbeats 6400000 in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (Θ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral R)
    (hRlev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K,
      R.toFun (g * k) = R.toFun g)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hfT : IsFactorizableTestFn K f)
    (S Sf Sψ : Finset (HeightOneSpectrum (𝓞 K))) (hSf : Sf ⊆ S) (hSψ : Sψ ⊆ S)
    (hfsupp : ∀ z : AdelicGL2 (𝓞 K) K, f z ≠ 0 →
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
        finComponent (𝓞 K) K v (glFin (𝓞 K) K z) ∈ localIntegralSet K v) ∧
      ∃ z₁ z₂ : AdelicGL2 (𝓞 K) K, z = z₁ * z₂ ∧
        z₂ ∈ levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K ∧
        ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf → ∀ xv : GL (Fin 2) (v.adicCompletion K),
          z₁ * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * z₁)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ¬ v.asIdeal ∣ Θ.level ∧ v ∉ R.exceptionalSet)
    (hSψ0 : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sψ →
      LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K v) = 0)
    (hfbi : ∀ k ∈ levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K, ∀ z : AdelicGL2 (𝓞 K) K,
      f (k * z) = f z ∧ f (z * k) = f z)
    (hx₀ : IsSmoothCuspAutomorphicFnAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) R.centralChar (rightConv K R.toFun f))
    (hne : ∃ g : AdelicGL2 (𝓞 K) K, rightConv K R.toFun f g ≠ 0) :
    ∃ (t₀ : (AdeleRing (𝓞 K) K)ˣ) (k₀ : AdelicGL2 (𝓞 K) K),
      k₀ ∈ maximalCompactAt K S ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((t₀ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1) ∧
      whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) 1 (diagOne t₀ * k₀) ≠ 0 := by
  have hN : Θ.level ≠ ⊥ := Θ.level_ne_bot
  have hRne : ∃ g, R.toFun g ≠ 0 := R.exists_ne_zero
  have hS_good := hS
  obtain ⟨g₀, hx₀ne⟩ := hne
  set ωR : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom with hωRdef
  have hωR_apply : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ωR z = R.centralChar ⟨z, Subgroup.mem_top z⟩ := fun z => rfl
  have hx₀1 := hx₀
  have hx₀c : Continuous (rightConv K R.toFun f) :=
    (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn K R.toFun hR f hfT).1
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

  have hx₀Z : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      rightConv K R.toFun f (centralScalar (𝓞 K) K z * g) =
        ((R.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * rightConv K R.toFun f g := by
    letI := (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).mS
    letI : MeasureSpace (AdelicGL2 (𝓞 K) K) := ⟨(productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).μ⟩
    intro z g
    exact hx₀1.1.1.central_transform ⟨z, Subgroup.mem_top z⟩ g
  have PKG₀ := fun (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) =>
    AutomorphicForm.SmoothCuspRealizationAt.unramified_package_rightConv_sum_translate
      K c u d₁ d₂ T Θ R hR hRlev f hfT S Sf Sψ hSf hSψ hfsupp hS hSψ0 1 (fun _ => 1) (fun _ => 1) (fun _ => map_one _)
      (fun _ v _ xv => by rw [one_mul, mul_one]) (rightConv K R.toFun f) (fun g => by simp) hx₀int hx₀per hx₀Z v hv
  set Wx₀ : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ := RS27.W1 K c u d₁ d₂ T (rightConv K R.toFun f) with hWx₀
  have locAll : ∀ v : HeightOneSpectrum (𝓞 K), ∃ (ψv : AddChar (v.adicCompletion K) ℂ) (ϖ : v.adicCompletionIntegers K)
      (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
      (b : Fin (Ideal.absNorm v.asIdeal) → v.adicCompletionIntegers K), v ∉ S →
        UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.diagZ
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ 1) = heckeGen (𝓞 K) K v ∧
        Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ) ∧
        (∀ r : v.adicCompletionIntegers K, ψv (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) = 1) ∧
        (∃ r : v.adicCompletionIntegers K, ψv (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r /
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) ≠ 1) ∧
        (∀ (xv : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
          Wx₀ (UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.unipotent xv) * g) = ψv xv * Wx₀ g) ∧
        (∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
          Wx₀ (g * UnramifiedWhittaker.placeEmbed K v (Matrix.GeneralLinearGroup.map
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = Wx₀ g) ∧
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∑ i, Wx₀ (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.repSome
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b i))))) +
            Wx₀ (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.repInf
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = Θ.toRawCentral.a v * Wx₀ g) ∧
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          Wx₀ (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.scalarPi
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = Θ.toRawCentral.b v * Wx₀ g) := by
    intro v
    by_cases hv : v ∈ S
    · exact ⟨1, 1, by simp, fun _ => 0, fun h => (h hv).elim⟩
    · obtain ⟨ψv, ϖ, hπ, b, hrest⟩ := (PKG₀ v hv).2
      exact ⟨ψv, ϖ, hπ, b, fun _ => hrest⟩
  choose ψloc ϖloc hπloc bloc hloc using locAll

  have hW₀ne : ∃ g, Wx₀ g ≠ 0 := by
    have hcusp0 : ∀ g, whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) 0 g = 0 := by
      intro g
      rw [whittakerCoefficient_zero_eq_constantTerm]
      exact hx₀1.1.2 g
    have hsum := AutomorphicForm.hasSum_whittakerCoefficient_one_diagOne_principalIdeles_mul K
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) (NumberField.StandardAddChar.stdAddChar K)
      (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K) (rightConv K R.toFun f) hx₀c hx₀G hx₀1.2
      (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn K R.toFun hR f hfT).2 hcusp0 g₀
    by_contra hall
    push_neg at hall
    have h0 : (fun γ : ↥(M4aHerbrand.principalIdeles (𝓞 K) K) =>
        whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) 1
          (diagOne (γ : (AdeleRing (𝓞 K) K)ˣ) * g₀)) = fun _ => 0 := funext fun γ => hall _
    rw [h0] at hsum
    exact hx₀ne (hsum.unique hasSum_zero)

  haveI : ∀ v : HeightOneSpectrum (𝓞 K), Nonempty (Fin (Ideal.absNorm v.asIdeal)) := fun v =>
    ⟨⟨0, Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)⟩⟩
  have hSN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ Θ.level → v ∈ S := fun v hvN => by
    by_contra hv; exact (hS_good v hv).1 hvN
  have hK₀ : ∀ k : GL (Fin 2) (AdeleRing (𝓞 K) K), k ∈ levelOne (𝓞 K) K ⊤ ⊓ finiteAdelicGL2Subgroup K →
      (∀ v ∈ S, ∀ i j : Fin 2, ((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v =
        ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v) →
      ∀ g, Wx₀ (g * k) = Wx₀ g := by
    intro k hk hkS g
    have hkN := RS27.mem_levelOne_of_trivial_at K Θ.level hN S hSN k hk hkS
    exact RS12W.whittakerCoefficient_mul_right_eq_of_forall K _ _ _ 1 g k (fun y => hx₀lev y k hkN)
  obtain ⟨g₁, a₁, hg₁, ha₁, hW₁⟩ :=
    UnramifiedWhittaker.exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero K S Wx₀ ψloc ϖloc hπloc
      (fun v hv => (hloc v hv).2.1) bloc (fun v => Θ.toRawCentral.a v) (fun v => Θ.toRawCentral.b v)
      (fun v hv => (hloc v hv).2.2.1) (fun v hv => (hloc v hv).2.2.2.1) (fun v hv => (hloc v hv).2.2.2.2.1)
      (fun v hv => (hloc v hv).2.2.2.2.2.2.1) (fun v hv => (hloc v hv).2.2.2.2.2.2.2) hK₀ hW₀ne

  obtain ⟨t₀, k₀, hk₀, ht₀, hWpt⟩ :=
    AutomorphicForm.exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero K S Wx₀
      (NumberField.StandardAddChar.stdAddChar K) ωR
      (fun uu g => by
        have hh := AutomorphicForm.whittakerCoefficient_unipotentGL2_mul K
          (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (NumberField.StandardAddChar.stdAddChar K)
          (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K).principalInvariant (rightConv K R.toFun f) g
          (fun β u' => hx₀per β u' g) 1 uu
        simpa only [map_one, one_mul] using hh)
      (fun z g => by
        rw [← RS12L_e13.centralScalar_comm K z g]
        exact RS12W.whittakerCoefficient_mul_central K _ _ (rightConv K R.toFun f) 1 g _ _
          (RS12L_e13.centralScalar_comm K z) (fun hh => by rw [hx₀Z z hh, hωR_apply]))
      (diagOne a₁ * g₁)
      (fun v hv => RS27.snd_apply_mul_of_trivial K _ _ v (RS27.snd_apply_diagOne_of_snd_eq_one K a₁ v (ha₁ v hv)) (hg₁ v hv))
      hW₁
  exact ⟨t₀, k₀, hk₀, ht₀, hWpt⟩

end S_AutomorphicForm_SmoothCuspRealizationAt_exists_mem_maximalCompactAt_whittakerCoefficient_rightConv_diagOne_mul_ne_zero
end P2MW
export P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_mem_maximalCompactAt_whittakerCoefficient_rightConv_diagOne_mul_ne_zero (solution)
