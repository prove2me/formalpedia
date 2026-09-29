-- Prove2me | solution 1 for AutomorphicForm.WhittakerModel.exists_forall_diagOne_eq_zero_of_lt_modulus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/9d7a5dfe-a34c-5d7e-958f-190e64736b8c

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_WhittakerModel_exists_forall_diagOne_eq_zero_of_lt_modulus
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal NumberField.AdelicLevel

namespace KBE1Aux

open Matrix NumberField.StandardAddChar

section Algebra

variable {K : Type*} [Field K]

theorem unipotent_val (x : K) : ((unipotent x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, x; 0, 1] := rfl

theorem diagOne_val (a : Kˣ) : ((diagOne a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![(a : K), 0; 0, 1] := by
  ext i j
  rw [diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem unipotent_mul_unipotent (s t : K) : unipotent s * unipotent t = unipotent (s + t) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Matrix.GeneralLinearGroup.coe_mul, unipotent_val, unipotent_val, unipotent_val, Matrix.mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp [add_comm]

@[scoped simp] theorem unipotent_zero : unipotent (0 : K) = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [unipotent_val, Matrix.GeneralLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp

theorem unipotent_inv (t : K) : (unipotent t)⁻¹ = unipotent (-t) := by
  apply inv_eq_of_mul_eq_one_right
  rw [unipotent_mul_unipotent, add_neg_cancel, unipotent_zero]

theorem diagOne_mul_unipotent (y : Kˣ) (t : K) :
    diagOne y * unipotent t = unipotent ((y : K) * t) * diagOne y := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, unipotent_val, unipotent_val,
    diagOne_val, Matrix.mul_fin_two, Matrix.mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp

end Algebra

section Topology

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]

theorem continuous_unipotent : Continuous (fun t : K => unipotent t) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · change Continuous (fun t : K => ((unipotent t : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
    simp_rw [unipotent_val]
    refine continuous_pi (fun i => continuous_pi (fun j => ?_))
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · change Continuous (fun t : K => (((unipotent t)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
    simp_rw [unipotent_inv, unipotent_val]
    refine continuous_pi (fun i => continuous_pi (fun j => ?_))
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

end Topology

end KBE1Aux
p2m_reactivate "P2MW.S_AutomorphicForm_WhittakerModel_exists_forall_diagOne_eq_zero_of_lt_modulus.KBE1Aux"

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (W : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      W (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * W g)
    (hsm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : (p.adicCompletion ℚ)ˣ, c < modulus (y : p.adicCompletion ℚ) → W (diagOne y) = 0 := by
  classical
  obtain ⟨U, hUopen, hU⟩ := hsm

  have h1 : (1 : GL (Fin 2) (p.adicCompletion ℚ)) ∈ U := U.one_mem
  have hT : {t : p.adicCompletion ℚ | unipotent t ∈ U} ∈ nhds (0 : p.adicCompletion ℚ) := by
    refine (hUopen.preimage KBE1Aux.continuous_unipotent).mem_nhds ?_
    show unipotent (0 : p.adicCompletion ℚ) ∈ U
    rw [KBE1Aux.unipotent_zero]
    exact h1
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hT

  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p u₀ ≠ 1 := by
    by_contra h
    have h' : ∀ x, NumberField.StandardAddChar.psiLocal ℚ p x = 1 := fun x => not_not.mp (not_exists.mp h x)
    exact LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p
      (DFunLike.ext _ _ (fun x => by rw [h' x, AddChar.one_apply]))
  have hu₀ne : u₀ ≠ 0 := by
    rintro rfl
    exact hu₀ (AddChar.map_zero_eq_one _)
  have hu₀pos : 0 < ‖u₀‖ := norm_pos_iff.mpr hu₀ne
  refine ⟨‖u₀‖ / ε, div_pos hu₀pos hε, fun y hy => ?_⟩

  have key : ∀ t : p.adicCompletion ℚ, ‖t‖ < ε →
      W (diagOne y) = NumberField.StandardAddChar.psiLocal ℚ p ((y : p.adicCompletion ℚ) * t) * W (diagOne y) := by
    intro t ht
    have htU : unipotent t ∈ U := hball (by simpa using ht)
    calc W (diagOne y) = W (diagOne y * unipotent t) := (hU _ htU _).symm
      _ = W (unipotent ((y : p.adicCompletion ℚ) * t) * diagOne y) := by
          rw [KBE1Aux.diagOne_mul_unipotent]
      _ = _ := hlaw _ _
  by_contra hW

  have hy' : ‖u₀‖ / ε < ‖(y : p.adicCompletion ℚ)‖ := by
    have := hy
    rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, coe_nnnorm] at this
    exact this
  have hypos : 0 < ‖(y : p.adicCompletion ℚ)‖ := lt_trans (div_pos hu₀pos hε) hy'
  have hy'' : ‖u₀‖ < ‖(y : p.adicCompletion ℚ)‖ * ε := (div_lt_iff₀ hε).mp hy'
  have ht : ‖(y : p.adicCompletion ℚ)⁻¹ * u₀‖ < ε := by
    rw [norm_mul, norm_inv, inv_mul_lt_iff₀ hypos]
    linarith [mul_comm ‖(y : p.adicCompletion ℚ)‖ ε]
  have h := key _ ht
  rw [← mul_assoc, mul_inv_cancel₀ (norm_pos_iff.mp hypos), one_mul] at h
  exact hW (by
    have h2 : (NumberField.StandardAddChar.psiLocal ℚ p u₀ - 1) * W (diagOne y) = 0 := by
      rw [sub_mul, one_mul, ← h, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (sub_eq_zero.mp h3) hu₀
    · exact h3)

end S_AutomorphicForm_WhittakerModel_exists_forall_diagOne_eq_zero_of_lt_modulus
end P2MW
export P2MW.S_AutomorphicForm_WhittakerModel_exists_forall_diagOne_eq_zero_of_lt_modulus (solution)
