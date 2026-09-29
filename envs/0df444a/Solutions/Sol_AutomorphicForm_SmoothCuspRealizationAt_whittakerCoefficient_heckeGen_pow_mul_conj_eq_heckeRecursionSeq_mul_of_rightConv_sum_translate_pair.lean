-- Prove2me | solution 1 for AutomorphicForm.SmoothCuspRealizationAt.whittakerCoefficient_heckeGen_pow_mul_conj_eq_heckeRecursionSeq_mul_of_rightConv_sum_translate_pair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/e34c06b9-6818-59ae-994a-cb295a5a87ee

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Theorems.Thm_AutomorphicForm_heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps
import Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Theorems.Thm_UnramifiedWhittaker_mul_conj_apply_heckeGen_pow_mul_eq_of_shell_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_whittakerCoefficient_heckeGen_pow_mul_conj_eq_heckeRecursionSeq_mul_of_rightConv_sum_translate_pair
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

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

namespace RSJWK

variable (K : Type) [Field K] [NumberField K]

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

theorem mul_comm_of_glArch_eq_one_of_glFin_eq_one {a b : AdelicGL2 (𝓞 K) K} (ha : glArch (𝓞 K) K a = 1)
    (hb : glFin (𝓞 K) K b = 1) : a * b = b * a :=
  gl_ext K (by rw [map_mul, map_mul, ha, one_mul, mul_one])
    (fun u => by rw [map_mul, map_mul, map_mul, map_mul, hb, map_one, mul_one, one_mul])

theorem placeEmbed_mul_comm_of_glFin_eq_one (v : HeightOneSpectrum (𝓞 K)) (xv : GL (Fin 2) (v.adicCompletion K))
    (k : AdelicGL2 (𝓞 K) K) (hk : glFin (𝓞 K) K k = 1) :
    UnramifiedWhittaker.placeEmbed K v xv * k = k * UnramifiedWhittaker.placeEmbed K v xv := by
  have hP : UnramifiedWhittaker.placeEmbed K v xv = AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K v xv) := rfl
  refine mul_comm_of_glArch_eq_one_of_glFin_eq_one K ?_ hk
  rw [hP, AdelicDock.glArch_finEmbed]

end RSJWK

set_option maxHeartbeats 6400000 in
theorem RSJW_family_laws
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
    (r : ℕ) (h : Fin r → AdelicGL2 (𝓞 K) K) (cs : Fin r → ℂ)
    (hharch : ∀ i, glArch (𝓞 K) K (h i) = 1)
    (hhcomm : ∀ i, ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ xv : GL (Fin 2) (v.adicCompletion K),
      h i * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * h i)
    (x : AdelicGL2 (𝓞 K) K → ℂ)
    (hxsum : ∀ g, x g = ∑ i, cs i * rightConv K R.toFun f (g * h i))
    (hxint : ∀ (α' : K) (g : AdelicGL2 (𝓞 K) K), WhittakerCoefficientIntegrable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
      (NumberField.StandardAddChar.stdAddChar K) x α' g)
    (hxper : ∀ (β : K) (uu : AdeleRing (𝓞 K) K) (hh : AdelicGL2 (𝓞 K) K),
      x (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + uu) * hh) = x (unipotentGL2 uu * hh))
    (hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x (centralScalar (𝓞 K) K z * g) = ((R.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x g)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S)
    (ϖ : v.adicCompletionIntegers K)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hϖval : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (hgen' : AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K v (LocalGL2.diagPi ϖ hϖ0)) = heckeGen (𝓞 K) K v)
    (sec : 𝓞 K ⧸ v.asIdeal → 𝓞 K)
    (hsec : ∀ c : 𝓞 K ⧸ v.asIdeal, Ideal.Quotient.mk v.asIdeal (sec c) = c)
    (hsysAll : ∀ M : Ideal (𝓞 K), ¬ v.asIdeal ∣ M →
      HeckeIntegralSeam.IsHeckeCosetSystem
        (levelOne (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (heckeGen (𝓞 K) K v)
        (fun i : Option (𝓞 K ⧸ v.asIdeal) =>
          AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K v
            (i.elim (LocalGL2.localRepInf ϖ hϖ0)
              (fun c => LocalGL2.localRepSome ϖ hϖ0
                (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec c)))))))
    [Fintype (𝓞 K ⧸ v.asIdeal)]
    (eI : (𝓞 K ⧸ v.asIdeal) ≃ Fin (Ideal.absNorm v.asIdeal)) :
      UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.diagZ
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hϖ0 1) = heckeGen (𝓞 K) K v ∧
      Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ) ∧
      (∀ r : v.adicCompletionIntegers K, (NumberField.StandardAddChar.psiLocal K v) (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) = 1) ∧
      (∃ r : v.adicCompletionIntegers K, (NumberField.StandardAddChar.psiLocal K v) (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r /
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) ≠ 1) ∧
      (∀ (xv : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
        whittakerCoefficient K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 (UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.unipotent xv) * g) = (NumberField.StandardAddChar.psiLocal K v) xv * whittakerCoefficient K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 g) ∧
      (∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
        whittakerCoefficient K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 (g * UnramifiedWhittaker.placeEmbed K v (Matrix.GeneralLinearGroup.map
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = whittakerCoefficient K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 g) ∧
      (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
        (∑ i, whittakerCoefficient K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.repSome
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hϖ0
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec (eI.symm i))))))) +
          whittakerCoefficient K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.repInf
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hϖ0)) = Θ.toRawCentral.a v * whittakerCoefficient K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 g) ∧
      (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
        whittakerCoefficient K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.scalarPi
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hϖ0)) = Θ.toRawCentral.b v * whittakerCoefficient K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 g)  := by
  have hN : Θ.level ≠ ⊥ := Θ.level_ne_bot
  have hRne : ∃ g, R.toFun g ≠ 0 := R.exists_ne_zero
  have hS_good := hS
  have hSf_sub := hSf
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
  have hconv : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      (∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
        x (g * UnramifiedWhittaker.placeEmbed K v (Matrix.GeneralLinearGroup.map
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = x g) ∧
      IsHeckeCosetEigenfunctionAt K (levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K)
        (heckeGen (𝓞 K) K v) v x (Θ.toRawCentral.a v) := by
    intro v hv
    obtain ⟨reps, hsys, hpr⟩ := hpure v hv
    obtain ⟨hlv, hev⟩ := hS_good v hv
    have hint : ∀ g : AdelicGL2 (𝓞 K) K, Integrable (fun z => R.toFun (g * z) * f z) (adelicGLHaar (Fin 2) (𝓞 K) K) := by
      intro g
      obtain ⟨hfc, hfcs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K f hfT
      haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
      exact ((hR.comp (continuous_mul_left g)).mul hfc).integrable_of_hasCompactSupport hfcs.mul_left
    have hsupp' : ∀ z : AdelicGL2 (𝓞 K) K, f z ≠ 0 → ∃ z₁ z₂ : AdelicGL2 (𝓞 K) K,
        z = z₁ * z₂ ∧ z₂ ∈ levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K ∧
        ∀ xv : GL (Fin 2) (v.adicCompletion K), z₁ * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * z₁ := by
      intro z hz
      obtain ⟨-, z₁, z₂, hzz, hz₂, hcommz⟩ := hfsupp z hz
      exact ⟨z₁, z₂, hzz, hz₂, hcommz v (fun hvS => hv (hSf_sub hvS))⟩
    have key := AutomorphicForm.heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps K v
      (levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K) (hUv v hv) reps hsys hpr R.toFun
      (fun g k hk => hRlev g k hk) (Θ.toRawCentral.a v) ?_ f hsupp' hint h cs (fun i xv => hhcomm i v hv xv)
    · obtain ⟨hK, -, hHecke⟩ := key
      refine ⟨fun kv g => ?_, ?_⟩
      · rw [hxsum, hxsum]; exact hK kv g
      ·
        have hfun : x = fun g => ∑ i, cs i * rightConv K R.toFun f (g * h i) := funext hxsum
        rw [hfun]; exact hHecke
    ·
      exact R.hecke_eigen v hev
  set Wx : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ := fun g => whittakerCoefficient K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 g with hWx
  have locdata :
      UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.diagZ
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hϖ0 1) = heckeGen (𝓞 K) K v ∧
      Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ) ∧
      (∀ r : v.adicCompletionIntegers K, (NumberField.StandardAddChar.psiLocal K v) (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) = 1) ∧
      (∃ r : v.adicCompletionIntegers K, (NumberField.StandardAddChar.psiLocal K v) (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r /
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) ≠ 1) ∧
      (∀ (xv : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
        Wx (UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.unipotent xv) * g) = (NumberField.StandardAddChar.psiLocal K v) xv * Wx g) ∧
      (∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
        Wx (g * UnramifiedWhittaker.placeEmbed K v (Matrix.GeneralLinearGroup.map
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = Wx g) ∧
      (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
        (∑ i, Wx (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.repSome
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hϖ0
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec (eI.symm i))))))) +
          Wx (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.repInf
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hϖ0)) = Θ.toRawCentral.a v * Wx g) ∧
      (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
        Wx (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.scalarPi
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hϖ0)) = Θ.toRawCentral.b v * Wx g) := by
    obtain ⟨hlv, hev⟩ := hS_good v hv
    have hvψ : v ∉ Sψ := fun h' => hv (hSψ h')

    have hgen : UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.diagZ
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hϖ0 1) = heckeGen (𝓞 K) K v := by
      rw [RS12L.diagZ_one_eq_diagPi]; exact hgen'
    have hcard : Fintype.card (𝓞 K ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
      rw [← Nat.card_eq_fintype_card, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    set b : Fin (Ideal.absNorm v.asIdeal) → v.adicCompletionIntegers K :=
      fun i => algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec (eI.symm i)) with hb

    set π : v.adicCompletion K := algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ with hπdef
    set repsO : Option (𝓞 K ⧸ v.asIdeal) → AdelicGL2 (𝓞 K) K := fun o =>
      UnramifiedWhittaker.placeEmbed K v (o.elim (UnramifiedWhittaker.repInf π hϖ0)
        (fun c' => UnramifiedWhittaker.repSome π hϖ0
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
            (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec c'))))) with hrepsO
    have hrepsO_eq : repsO = fun o : Option (𝓞 K ⧸ v.asIdeal) => AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K v
        (o.elim (LocalGL2.localRepInf ϖ hϖ0) (fun c' => LocalGL2.localRepSome ϖ hϖ0
          (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec c'))))) := by
      funext o
      cases o with
      | none => simp only [hrepsO, Option.elim]; rw [RS12L.repInf_eq_localRepInf]; rfl
      | some c' => simp only [hrepsO, Option.elim]; rw [RS12L.repSome_eq_localRepSome]; rfl
    have hsysO : IsHeckeCosetSystem (levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K) (heckeGen (𝓞 K) K v) repsO := by
      rw [hrepsO_eq]; exact hsysAll Θ.level hlv

    have hcardO : Fintype.card (Option (𝓞 K ⧸ v.asIdeal)) = Ideal.absNorm v.asIdeal + 1 := by
      rw [Fintype.card_option, hcard]
    set eO : Option (𝓞 K ⧸ v.asIdeal) ≃ Fin (Ideal.absNorm v.asIdeal + 1) := Fintype.equivFinOfCardEq hcardO with heO
    have hsysF := RS12H.isHeckeCosetSystem_comp_equiv repsO eO.symm hsysO
    have hprF : ∀ j, ∃ m : GL (Fin 2) (v.adicCompletion K), (repsO ∘ eO.symm) j = UnramifiedWhittaker.placeEmbed K v m := by
      intro j
      simp only [Function.comp, hrepsO]
      exact ⟨_, rfl⟩
    obtain ⟨hfc, hfcs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K f hfT
    haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
    have hintf : ∀ g : AdelicGL2 (𝓞 K) K, Integrable (fun z => R.toFun (g * z) * f z) (adelicGLHaar (Fin 2) (𝓞 K) K) :=
      fun g => ((hR.comp (continuous_mul_left g)).mul hfc).integrable_of_hasCompactSupport hfcs.mul_left
    have hsupp' : ∀ z : AdelicGL2 (𝓞 K) K, f z ≠ 0 → ∃ z₁ z₂ : AdelicGL2 (𝓞 K) K,
        z = z₁ * z₂ ∧ z₂ ∈ levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K ∧
        ∀ xv : GL (Fin 2) (v.adicCompletion K), z₁ * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * z₁ := by
      intro z hz
      obtain ⟨-, z₁, z₂, hzz, hz₂, hcommz⟩ := hfsupp z hz
      exact ⟨z₁, z₂, hzz, hz₂, hcommz v (fun hvS => hv (hSf_sub hvS))⟩
    obtain ⟨-, hsumreps, -⟩ := AutomorphicForm.heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps K v
      (levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K) (hUv v hv) (repsO ∘ eO.symm) hsysF hprF R.toFun
      (fun g k hk => hRlev g k hk) (Θ.toRawCentral.a v) (R.hecke_eigen v hev) f hsupp' hintf h cs (fun i xv => hhcomm i v hv xv)

    have hsumO : ∀ hh : AdelicGL2 (𝓞 K) K, (∑ o, x (hh * repsO o)) = Θ.toRawCentral.a v * x hh := by
      intro hh
      have h1 := hsumreps hh
      simp only [heckeCosetSum] at h1
      rw [← hxsum hh] at h1
      have h2 : (∑ j, ∑ i, cs i * rightConv K R.toFun f (hh * (repsO ∘ eO.symm) j * h i)) = ∑ j, x (hh * (repsO ∘ eO.symm) j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hxsum]
      rw [h2] at h1
      rw [← h1]
      exact (Equiv.sum_comp eO.symm (fun o => x (hh * repsO o))).symm

    set ψv : AddChar (v.adicCompletion K) ℂ := NumberField.StandardAddChar.psiLocal K v with hψvdef
    have hψ0 : ∀ r : v.adicCompletionIntegers K, ψv (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) = 1 :=
      fun r => LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers K v _ r.2
    have hψ1 : ∃ r : v.adicCompletionIntegers K, ψv (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r / π) ≠ 1 := by
      have hlev0 := hSψ0 v hvψ
      obtain ⟨-, xx, hxx, hxx1⟩ := LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel K v ψv
        ⟨0, fun y hy => LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers K v y (by
          rwa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, ← WithZero.exp_zero])⟩
        (LanglandsTunnell.TateLocal.psiLocal_ne_one K v)
      rw [hlev0, zero_add] at hxx
      have hππ : (π : v.adicCompletion K) = (ϖ : v.adicCompletion K) := rfl
      have hvπ : Valued.v π = WithZero.exp (-1 : ℤ) := by rw [hππ]; exact hϖval
      have hr : xx * π ∈ v.adicCompletionIntegers K := by
        rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hvπ]
        calc Valued.v xx * WithZero.exp (-1 : ℤ) ≤ WithZero.exp 1 * WithZero.exp (-1 : ℤ) :=
              mul_le_mul_left hxx _
          _ = 1 := by rw [← WithZero.exp_add]; norm_num
      refine ⟨⟨xx * π, hr⟩, ?_⟩
      have hπ0 : π ≠ 0 := hϖ0
      rwa [show algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ⟨xx * π, hr⟩ = xx * π from rfl,
        mul_div_cancel_right₀ _ hπ0]

    have hNw : ∀ (xv : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
        Wx (UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.unipotent xv) * g) = ψv xv * Wx g := by
      intro xv g
      simp only [hWx]
      rw [RS12L.placeEmbed_unipotent, AutomorphicForm.whittakerCoefficient_unipotentGL2_mul K _ _ _ _
        (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K).principalInvariant x g (fun β uu => hxper β uu g) 1]
      congr 1
      rw [map_one, one_mul]
      rfl
    have hKw : ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
        Wx (g * UnramifiedWhittaker.placeEmbed K v (Matrix.GeneralLinearGroup.map
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = Wx g :=
      fun kv g => RS12W.whittakerCoefficient_mul_right_eq_of_forall K _ _ x 1 g _ (fun y => (hconv v hv).1 kv y)
    have hTw : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
        (∑ i, Wx (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.repSome π hϖ0
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b i))))) +
          Wx (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.repInf π hϖ0)) = Θ.toRawCentral.a v * Wx g := by
      intro g
      have hWsum := RS12W.sum_whittakerCoefficient_mul_right_eq K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K)
        x 1 g repsO (Θ.toRawCentral.a v) hsumO (fun o => by
          simpa [WhittakerCoefficientIntegrable, mul_assoc] using hxint 1 (g * repsO o))
      simp only [hWx] at hWsum ⊢
      rw [Fintype.sum_option] at hWsum
      rw [add_comm, ← hWsum]
      congr 1
      simp only [hrepsO, hb, Option.elim]
      exact Equiv.sum_comp eI.symm (fun c' => whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
        (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.repSome π hϖ0
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
            (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec c'))))))
    have hZw : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
        Wx (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.scalarPi π hϖ0)) = Θ.toRawCentral.b v * Wx g := by
      intro g
      rw [RS12L_e13.placeEmbed_scalarPi]
      set z : (AdeleRing (𝓞 K) K)ˣ := RS12L_e13.zIdele K v π hϖ0 with hzdef
      have hz : Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v) = z := by
        rw [← hgen]; exact RS12L_e13.det_placeEmbed_diagZ_one K v π hϖ0

      have hRZ : ∀ g' : AdelicGL2 (𝓞 K) K, R.toFun (centralScalar (𝓞 K) K z * g') =
          ((R.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * R.toFun g' := by
        letI := (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (adelicBox K)).mS
        letI : MeasureSpace (AdelicGL2 (𝓞 K) K) := ⟨(productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (adelicBox K)).μ⟩
        intro g'
        exact R.smoothCusp.1.1.central_transform ⟨z, Subgroup.mem_top z⟩ g'
      have hRb : ∀ g' : AdelicGL2 (𝓞 K) K, R.toFun (centralScalar (𝓞 K) K z * g') = Θ.toRawCentral.b v * R.toFun g' := by
        intro g'
        have := R.central_eigen v hev g'
        rwa [show Matrix.GeneralLinearGroup.det ((productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (adelicBox K)).gen v) = z from hz] at this
      obtain ⟨g', hg'⟩ := hRne
      have hξb : ((R.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) = Θ.toRawCentral.b v :=
        mul_right_cancel₀ hg' ((hRZ g').symm.trans (hRb g'))
      simp only [hWx]
      exact RS12W.whittakerCoefficient_mul_central K _ _ x 1 g _ _ (RS12L_e13.centralScalar_comm K z)
        (fun hh => by rw [hxZ z hh, hξb])
    exact ⟨hgen, hϖval, hψ0, hψ1, hNw, hKw, hTw, hZw⟩
  exact locdata

set_option maxHeartbeats 6400000 in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (S Sψ : Finset (HeightOneSpectrum (𝓞 K))) (_hSψ : Sψ ⊆ S)
    (_hSψ0 : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sψ →
      LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K v) = 0)
    (Θ₁ : HeckeEigensystem K ℂ)
    (R₁ : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ₁.toRawCentral)
    (_hR₁ : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ₁.toRawCentral R₁)
    (_hRlev₁ : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K Θ₁.level ⊓ finiteAdelicGL2Subgroup K,
      R₁.toFun (g * k) = R₁.toFun g)
    (f₁ : AdelicGL2 (𝓞 K) K → ℂ) (_hfT₁ : IsFactorizableTestFn K f₁)
    (Sf₁ : Finset (HeightOneSpectrum (𝓞 K))) (_hSf₁ : Sf₁ ⊆ S)
    (_hfsupp₁ : ∀ z : AdelicGL2 (𝓞 K) K, f₁ z ≠ 0 →
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf₁ →
        finComponent (𝓞 K) K v (glFin (𝓞 K) K z) ∈ localIntegralSet K v) ∧
      ∃ z₁ z₂ : AdelicGL2 (𝓞 K) K, z = z₁ * z₂ ∧
        z₂ ∈ levelOne (𝓞 K) K Θ₁.level ⊓ finiteAdelicGL2Subgroup K ∧
        ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf₁ → ∀ xv : GL (Fin 2) (v.adicCompletion K),
          z₁ * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * z₁)
    (_hS₁ : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ¬ v.asIdeal ∣ Θ₁.level ∧ v ∉ R₁.exceptionalSet)
    (r₁ : ℕ) (h₁ : Fin r₁ → AdelicGL2 (𝓞 K) K) (cs₁ : Fin r₁ → ℂ)
    (_hharch₁ : ∀ i, glArch (𝓞 K) K (h₁ i) = 1)
    (_hhcomm₁ : ∀ i, ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ xv : GL (Fin 2) (v.adicCompletion K),
      h₁ i * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * h₁ i)
    (x₁ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hxsum₁ : ∀ g, x₁ g = ∑ i, cs₁ i * rightConv K R₁.toFun f₁ (g * h₁ i))
    (_hxint₁ : ∀ (α' : K) (g : AdelicGL2 (𝓞 K) K), WhittakerCoefficientIntegrable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
      (NumberField.StandardAddChar.stdAddChar K) x₁ α' g)
    (_hxper₁ : ∀ (β : K) (uu : AdeleRing (𝓞 K) K) (hh : AdelicGL2 (𝓞 K) K),
      x₁ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + uu) * hh) = x₁ (unipotentGL2 uu * hh))
    (_hxZ₁ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x₁ (centralScalar (𝓞 K) K z * g) = ((R₁.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x₁ g)
    (Θ₂ : HeckeEigensystem K ℂ)
    (R₂ : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ₂.toRawCentral)
    (_hR₂ : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ₂.toRawCentral R₂)
    (_hRlev₂ : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K Θ₂.level ⊓ finiteAdelicGL2Subgroup K,
      R₂.toFun (g * k) = R₂.toFun g)
    (f₂ : AdelicGL2 (𝓞 K) K → ℂ) (_hfT₂ : IsFactorizableTestFn K f₂)
    (Sf₂ : Finset (HeightOneSpectrum (𝓞 K))) (_hSf₂ : Sf₂ ⊆ S)
    (_hfsupp₂ : ∀ z : AdelicGL2 (𝓞 K) K, f₂ z ≠ 0 →
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf₂ →
        finComponent (𝓞 K) K v (glFin (𝓞 K) K z) ∈ localIntegralSet K v) ∧
      ∃ z₁ z₂ : AdelicGL2 (𝓞 K) K, z = z₁ * z₂ ∧
        z₂ ∈ levelOne (𝓞 K) K Θ₂.level ⊓ finiteAdelicGL2Subgroup K ∧
        ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf₂ → ∀ xv : GL (Fin 2) (v.adicCompletion K),
          z₁ * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * z₁)
    (_hS₂ : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ¬ v.asIdeal ∣ Θ₂.level ∧ v ∉ R₂.exceptionalSet)
    (r₂ : ℕ) (h₂ : Fin r₂ → AdelicGL2 (𝓞 K) K) (cs₂ : Fin r₂ → ℂ)
    (_hharch₂ : ∀ i, glArch (𝓞 K) K (h₂ i) = 1)
    (_hhcomm₂ : ∀ i, ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ xv : GL (Fin 2) (v.adicCompletion K),
      h₂ i * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * h₂ i)
    (x₂ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hxsum₂ : ∀ g, x₂ g = ∑ i, cs₂ i * rightConv K R₂.toFun f₂ (g * h₂ i))
    (_hxint₂ : ∀ (α' : K) (g : AdelicGL2 (𝓞 K) K), WhittakerCoefficientIntegrable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
      (NumberField.StandardAddChar.stdAddChar K) x₂ α' g)
    (_hxper₂ : ∀ (β : K) (uu : AdeleRing (𝓞 K) K) (hh : AdelicGL2 (𝓞 K) K),
      x₂ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + uu) * hh) = x₂ (unipotentGL2 uu * hh))
    (_hxZ₂ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x₂ (centralScalar (𝓞 K) K z * g) = ((R₂.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x₂ g)
    (v : HeightOneSpectrum (𝓞 K)) (_hv : v ∉ S)
    (k₁ k₂ : AdelicGL2 (𝓞 K) K) (_hk₁ : glFin (𝓞 K) K k₁ = 1) (_hk₂ : glFin (𝓞 K) K k₂ = 1)
    (g : AdelicGL2 (𝓞 K) K)
    (_hg : Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
      (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
           (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2)
    (m : ℕ) :
    whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₁ 1 ((heckeGen (𝓞 K) K v) ^ m * g * k₁) *
        (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₂ 1 ((heckeGen (𝓞 K) K v) ^ m * g * k₂)) =
      UnramifiedWhittaker.heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (Θ₁.toRawCentral.a v) (Θ₁.toRawCentral.b v) m *
        UnramifiedWhittaker.heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)
          ((starRingEnd ℂ) (Θ₂.toRawCentral.a v)) ((starRingEnd ℂ) (Θ₂.toRawCentral.b v)) m *
        (whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₁ 1 (g * k₁) *
          (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₂ 1 (g * k₂))) := by
  obtain ⟨ϖ, hϖ0, hϖval, hgen', sec, hsec, hsysAll⟩ := HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen K v
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  letI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 K ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [← Nat.card_eq_fintype_card, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  obtain ⟨eI⟩ : Nonempty ((𝓞 K ⧸ v.asIdeal) ≃ Fin (Ideal.absNorm v.asIdeal)) := ⟨Fintype.equivFinOfCardEq hcard⟩
  obtain ⟨hgen, -, hψ0, hψ1, hN1, hK1, hT1, hZ1⟩ := RSJW_family_laws K c u d₁ d₂ T Θ₁ R₁ _hR₁ _hRlev₁ f₁ _hfT₁ S Sf₁ Sψ _hSf₁ _hSψ _hfsupp₁ _hS₁ _hSψ0 r₁ h₁ cs₁ _hharch₁ _hhcomm₁ x₁ _hxsum₁ _hxint₁ _hxper₁ _hxZ₁ v _hv
    ϖ hϖ0 hϖval hgen' sec hsec hsysAll eI
  obtain ⟨-, -, -, -, hN2, hK2, hT2, hZ2⟩ := RSJW_family_laws K c u d₁ d₂ T Θ₂ R₂ _hR₂ _hRlev₂ f₂ _hfT₂ S Sf₂ Sψ _hSf₂ _hSψ _hfsupp₂ _hS₂ _hSψ0 r₂ h₂ cs₂ _hharch₂ _hhcomm₂ x₂ _hxsum₂ _hxint₂ _hxper₂ _hxZ₂ v _hv
    ϖ hϖ0 hϖval hgen' sec hsec hsysAll eI
  haveI : Nonempty (Fin (Ideal.absNorm v.asIdeal)) := by
    refine ⟨⟨0, ?_⟩⟩
    rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hI : Fintype.card (Fin (Ideal.absNorm v.asIdeal)) = Ideal.absNorm v.asIdeal := Fintype.card_fin _
  have hc₁ : ∀ xv : GL (Fin 2) (v.adicCompletion K), UnramifiedWhittaker.placeEmbed K v xv * k₁ = k₁ * UnramifiedWhittaker.placeEmbed K v xv :=
    fun xv => RSJWK.placeEmbed_mul_comm_of_glFin_eq_one K v xv k₁ _hk₁
  have hc₂ : ∀ xv : GL (Fin 2) (v.adicCompletion K), UnramifiedWhittaker.placeEmbed K v xv * k₂ = k₂ * UnramifiedWhittaker.placeEmbed K v xv :=
    fun xv => RSJWK.placeEmbed_mul_comm_of_glFin_eq_one K v xv k₂ _hk₂

  set W₁ : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ := fun X => whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₁ 1 (X * k₁) with hW₁
  set W₂ : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ := fun X => whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₂ 1 (X * k₂) with hW₂
  have hN1' : ∀ (xv : v.adicCompletion K) (X : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W₁ (UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.unipotent xv) * X) =
        (NumberField.StandardAddChar.psiLocal K v) xv * W₁ X := by
    intro xv X; simp only [hW₁, mul_assoc]; exact hN1 xv (X * k₁)
  have hN2' : ∀ (xv : v.adicCompletion K) (X : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W₂ (UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.unipotent xv) * X) =
        (NumberField.StandardAddChar.psiLocal K v) xv * W₂ X := by
    intro xv X; simp only [hW₂, mul_assoc]; exact hN2 xv (X * k₂)
  have hK1' : ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (X : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W₁ (X * UnramifiedWhittaker.placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = W₁ X := by
    intro kv X; simp only [hW₁]; rw [mul_assoc, hc₁, ← mul_assoc]; exact hK1 kv (X * k₁)
  have hK2' : ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (X : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W₂ (X * UnramifiedWhittaker.placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = W₂ X := by
    intro kv X; simp only [hW₂]; rw [mul_assoc, hc₂, ← mul_assoc]; exact hK2 kv (X * k₂)
  have hT1' : ∀ X : GL (Fin 2) (AdeleRing (𝓞 K) K),
      (∑ i, W₁ (X * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.repSome
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hϖ0
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
            ((fun i : Fin (Ideal.absNorm v.asIdeal) => algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec (eI.symm i))) i))))) +
        W₁ (X * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.repInf
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hϖ0)) = Θ₁.toRawCentral.a v * W₁ X := by
    intro X
    simp only [hW₁]
    have h := hT1 (X * k₁)
    simp only [mul_assoc, ← hc₁] at h
    simpa only [mul_assoc] using h
  have hT2' : ∀ X : GL (Fin 2) (AdeleRing (𝓞 K) K),
      (∑ i, W₂ (X * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.repSome
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hϖ0
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
            ((fun i : Fin (Ideal.absNorm v.asIdeal) => algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec (eI.symm i))) i))))) +
        W₂ (X * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.repInf
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hϖ0)) = Θ₂.toRawCentral.a v * W₂ X := by
    intro X
    simp only [hW₂]
    have h := hT2 (X * k₂)
    simp only [mul_assoc, ← hc₂] at h
    simpa only [mul_assoc] using h
  have hZ1' : ∀ X : GL (Fin 2) (AdeleRing (𝓞 K) K),
      W₁ (X * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.scalarPi
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hϖ0)) = Θ₁.toRawCentral.b v * W₁ X := by
    intro X; simp only [hW₁]; rw [mul_assoc, hc₁, ← mul_assoc]; exact hZ1 (X * k₁)
  have hZ2' : ∀ X : GL (Fin 2) (AdeleRing (𝓞 K) K),
      W₂ (X * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.scalarPi
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hϖ0)) = Θ₂.toRawCentral.b v * W₂ X := by
    intro X; simp only [hW₂]; rw [mul_assoc, hc₂, ← mul_assoc]; exact hZ2 (X * k₂)
  have key := (UnramifiedWhittaker.mul_conj_apply_heckeGen_pow_mul_eq_of_shell_zero K v
    (NumberField.StandardAddChar.psiLocal K v) ϖ hϖ0 hgen
    (fun i : Fin (Ideal.absNorm v.asIdeal) => algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec (eI.symm i))) hI hψ0 hψ1
    W₁ W₂ (Θ₁.toRawCentral.a v) (Θ₁.toRawCentral.b v) (Θ₂.toRawCentral.a v) (Θ₂.toRawCentral.b v)
    hN1' hN2' hK1' hK2' hT1' hT2' hZ1' hZ2' g _hg).1 m
  simpa only [hW₁, hW₂] using key

end
end S_AutomorphicForm_SmoothCuspRealizationAt_whittakerCoefficient_heckeGen_pow_mul_conj_eq_heckeRecursionSeq_mul_of_rightConv_sum_translate_pair
end P2MW
export P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_whittakerCoefficient_heckeGen_pow_mul_conj_eq_heckeRecursionSeq_mul_of_rightConv_sum_translate_pair (solution)
