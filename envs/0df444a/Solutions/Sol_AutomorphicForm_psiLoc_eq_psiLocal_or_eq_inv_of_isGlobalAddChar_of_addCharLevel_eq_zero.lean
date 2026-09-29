-- Prove2me | solution 1 for AutomorphicForm.psiLoc_eq_psiLocal_or_eq_inv_of_isGlobalAddChar_of_addCharLevel_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/b23f97be-ed52-52d7-9133-b3e07b2d9f82

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_RatIdele_Normalizer
import Theorems.Thm_AutomorphicForm_exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_CubicInduction_psiLoc_ne_one_and_level_clauses_of_isGlobalAddChar
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_psiLoc_eq_psiLocal_or_eq_inv_of_isGlobalAddChar_of_addCharLevel_eq_zero
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.Converse
open LanglandsTunnell.CubicInduction NumberField.StandardAddChar

namespace SignDich48

theorem psiLoc_eq_mul (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (a₀ : ℚ)
    (hψa₀ : ∀ x : AdeleRing (𝓞 ℚ) ℚ, ψ x = stdAddChar ℚ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a₀ * x))
    (v : HeightOneSpectrum (𝓞 ℚ)) (y : v.adicCompletion ℚ) :
    psiLoc ψ v y = psiLocal ℚ v (algebraMap ℚ (v.adicCompletion ℚ) a₀ * y) := by
  set a₀v : v.adicCompletion ℚ := algebraMap ℚ (v.adicCompletion ℚ) a₀ with ha₀v
  have hmul₀ : algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a₀ * adeleSingleAt ℚ v y = adeleSingleAt ℚ v (a₀v * y) := by
    rw [adeleSingleAt_apply, adeleSingleAt_apply]
    change ((algebraMap ℚ (InfiniteAdeleRing ℚ) a₀, algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) a₀) :
        InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) * ((0 : InfiniteAdeleRing ℚ), finAdeleSingleAt ℚ v y) =
      ((0 : InfiniteAdeleRing ℚ), finAdeleSingleAt ℚ v (a₀v * y))
    rw [Prod.mk_mul_mk, mul_zero]
    congr 1
    apply FiniteAdeleRing.ext ℚ
    intro w
    change (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) a₀) w * (finAdeleSingleAt ℚ v y) w = _
    by_cases hw : w = v
    · subst hw
      rw [finAdeleSingleAt_apply_self, finAdeleSingleAt_apply_self, FiniteAdeleRing.algebraMap_apply, ha₀v]
      rfl
    · rw [finAdeleSingleAt_apply_of_ne _ _ _ hw, finAdeleSingleAt_apply_of_ne _ _ _ hw, mul_zero]
  show ψ (adeleSingleAt ℚ v y) = stdAddChar ℚ (adeleSingleAt ℚ v (a₀v * y))
  rw [hψa₀, hmul₀]

theorem valued_eq_one (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) (a₀ : ℚ) (ha₀ : a₀ ≠ 0)
    (hψa₀ : ∀ x : AdeleRing (𝓞 ℚ) ℚ, ψ x = stdAddChar ℚ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a₀ * x))
    (v : HeightOneSpectrum (𝓞 ℚ)) (hlev : LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0) :
    Valued.v (algebraMap ℚ (v.adicCompletion ℚ) a₀) = 1 := by
  obtain ⟨-, -, hlev3⟩ := psiLoc_ne_one_and_level_clauses_of_isGlobalAddChar ψ hψ v
  obtain ⟨hψ0, x, hx, hx1⟩ := hlev3 hlev
  set a₀v : v.adicCompletion ℚ := algebraMap ℚ (v.adicCompletion ℚ) a₀ with ha₀v
  have ha₀v0 : a₀v ≠ 0 := by rw [ha₀v]; exact (map_ne_zero _).mpr ha₀
  have key : ∀ y, psiLoc ψ v y = psiLocal ℚ v (a₀v * y) := fun y => psiLoc_eq_mul ψ a₀ hψa₀ v y
  have hne0 : Valued.v a₀v ≠ 0 := (Valuation.ne_zero_iff _).mpr ha₀v0
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v a₀v = WithZero.exp m := ⟨_, (WithZero.exp_log hne0).symm⟩
  have hϖ : Valued.v (varpi v) = WithZero.exp (-1 : ℤ) := NumberField.AdelicLevel.valued_uniformizerUnit ℚ v
  have hint1 : ∀ y : v.adicCompletion ℚ, Valued.v y ≤ 1 → psiLocal ℚ v y = 1 := fun y hy =>
    LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ v y
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hy)
  obtain ⟨-, z, hz, hz1⟩ := LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ v
    (psiLocal ℚ v) ⟨0, fun y hy => hint1 y (by rwa [WithZero.exp_zero] at hy)⟩ (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ v)
  rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat v, zero_add] at hz
  have hm0 : ¬ (m ≤ -1) := by
    intro hm1
    apply hx1
    rw [key]
    apply hint1
    rw [map_mul, map_mul, map_inv₀, hm, hϖ, ← WithZero.exp_neg, neg_neg]
    calc WithZero.exp m * (WithZero.exp (1 : ℤ) * Valued.v x)
        ≤ WithZero.exp m * (WithZero.exp (1 : ℤ) * 1) := mul_le_mul_right (mul_le_mul_right hx _) _
      _ = WithZero.exp (m + 1) := by rw [mul_one, WithZero.exp_add]
      _ ≤ WithZero.exp 0 := WithZero.exp_le_exp.mpr (by omega)
      _ = 1 := WithZero.exp_zero
  have hm1 : ¬ (1 ≤ m) := by
    intro hm1
    apply hz1
    have hz' : z = a₀v * (a₀v⁻¹ * z) := by rw [mul_inv_cancel_left₀ ha₀v0]
    rw [hz', ← key]
    apply hψ0
    rw [map_mul, map_inv₀, hm, ← WithZero.exp_neg]
    calc WithZero.exp (-m) * Valued.v z ≤ WithZero.exp (-m) * WithZero.exp (1 : ℤ) := mul_le_mul_right hz _
      _ = WithZero.exp (-m + 1) := by rw [WithZero.exp_add]
      _ ≤ WithZero.exp 0 := WithZero.exp_le_exp.mpr (by omega)
      _ = 1 := WithZero.exp_zero
  have hm00 : m = 0 := by omega
  rw [hm, hm00, WithZero.exp_zero]

theorem eq_one_or_eq_neg_one (a₀ : ℚ) (ha₀ : a₀ ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v (algebraMap ℚ (v.adicCompletion ℚ) a₀) = 1) :
    a₀ = 1 ∨ a₀ = -1 := by
  have hval : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.valuation ℚ a₀ = 1 := fun v => by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact h v
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 ℚ) ℚ a₀ (fun v => (hval v).le)
  obtain ⟨r', hr'⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 ℚ) ℚ a₀⁻¹ (fun v => by
    rw [map_inv₀, hval v, inv_one])
  have hinj : Function.Injective (algebraMap (𝓞 ℚ) ℚ) := RingOfIntegers.coe_injective
  have hrr' : r * r' = 1 := by
    apply hinj
    rw [map_mul, hr, hr', map_one, mul_inv_cancel₀ ha₀]
  have hu : IsUnit (Rat.ringOfIntegersEquiv r) := by
    refine isUnit_iff_exists_inv.mpr ⟨Rat.ringOfIntegersEquiv r', ?_⟩
    rw [← map_mul, hrr', map_one]
  rcases Int.isUnit_iff.mp hu with h1 | h1
  · left
    have := Rat.ringOfIntegersEquiv_apply_coe r
    rw [h1, hr] at this
    exact_mod_cast this.symm
  · right
    have := Rat.ringOfIntegersEquiv_apply_coe r
    rw [h1, hr] at this
    exact_mod_cast this.symm

end SignDich48

open SignDich48 in
theorem solution
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    psiLoc ψ v = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ ∨
      psiLoc ψ v = NumberField.StandardAddChar.psiLocal ℚ v := by
  obtain ⟨a₀, ha₀, hψa₀⟩ := AutomorphicForm.exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar ℚ hψ
  have hunit : ∀ u : HeightOneSpectrum (𝓞 ℚ), Valued.v (algebraMap ℚ (u.adicCompletion ℚ) a₀) = 1 :=
    fun u => valued_eq_one ψ hψ a₀ ha₀ hψa₀ u (hlev u)
  rcases eq_one_or_eq_neg_one a₀ ha₀ hunit with h1 | h1
  · right
    ext y
    rw [psiLoc_eq_mul ψ a₀ hψa₀ v y, h1, map_one, one_mul]
  · left
    ext y
    rw [AddChar.inv_apply, psiLoc_eq_mul ψ a₀ hψa₀ v y, h1, map_neg, map_one, neg_one_mul]

end S_AutomorphicForm_psiLoc_eq_psiLocal_or_eq_inv_of_isGlobalAddChar_of_addCharLevel_eq_zero
end P2MW
export P2MW.S_AutomorphicForm_psiLoc_eq_psiLocal_or_eq_inv_of_isGlobalAddChar_of_addCharLevel_eq_zero (solution)
