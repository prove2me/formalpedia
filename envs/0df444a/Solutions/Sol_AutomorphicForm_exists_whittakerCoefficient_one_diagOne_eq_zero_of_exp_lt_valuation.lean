-- Prove2me | solution 1 for AutomorphicForm.exists_whittakerCoefficient_one_diagOne_eq_zero_of_exp_lt_valuation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/8feaa5c2-943c-5c30-933a-baea39adcce2

import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Theorems.Thm_AutomorphicForm_IsKfSmooth_exists_ideal_forall_apply_mul_conj_unipotentGL2_eq
import Theorems.Thm_AutomorphicForm_exists_localComponents_of_isGlobalAddChar
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_whittakerCoefficient_one_diagOne_eq_zero_of_exp_lt_valuation
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq"
p2m_attr_erase "simp" "SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm

noncomputable section

namespace Ws1
namespace K5a

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

def finSingle (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) : FiniteAdeleRing (𝓞 F) F :=
  ⟨Function.update (fun w : HeightOneSpectrum (𝓞 F) => (0 : w.adicCompletion F)) v y, by
    refine Filter.eventually_cofinite.mpr ?_
    refine (Set.finite_singleton v).subset ?_
    intro w hw
    simp only [Set.mem_setOf_eq] at hw
    by_contra hne
    apply hw
    rw [Function.update_of_ne hne]
    exact zero_mem _⟩

theorem finSingle_apply_self (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) :
    finSingle v y v = y := by
  show Function.update (fun w : HeightOneSpectrum (𝓞 F) => (0 : w.adicCompletion F)) v y v = y
  rw [Function.update_self]

theorem finSingle_apply_of_ne (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) : finSingle v y w = 0 := by
  show Function.update (fun w : HeightOneSpectrum (𝓞 F) => (0 : w.adicCompletion F)) v y w = 0
  rw [Function.update_of_ne hw]

theorem mul_finSingle (v : HeightOneSpectrum (𝓞 F)) (x : FiniteAdeleRing (𝓞 F) F) (y : v.adicCompletion F) :
    x * finSingle v y = finSingle v (x v * y) := by
  apply RestrictedProduct.ext
  intro w
  by_cases hw : w = v
  · subst hw
    change x w * finSingle w y w = finSingle w (x w * y) w
    rw [finSingle_apply_self, finSingle_apply_self]
  · change x w * finSingle v y w = finSingle v (x v * y) w
    rw [finSingle_apply_of_ne v y hw, finSingle_apply_of_ne v _ hw, mul_zero]

theorem finSingle_mem_idealBall (v : HeightOneSpectrum (𝓞 F)) {y : v.adicCompletion F} {N : Ideal (𝓞 F)}
    (hy : Valued.v y ≤ idealBound (𝓞 F) N v) : finSingle v y ∈ idealBall (𝓞 F) F N := by
  intro w
  by_cases hw : w = v
  · subst hw
    rwa [finSingle_apply_self]
  · rw [finSingle_apply_of_ne v y hw, map_zero]
    exact zero_le'

theorem finprod_finSingle (v : HeightOneSpectrum (𝓞 F))
    (ψv : (w : HeightOneSpectrum (𝓞 F)) → AddChar (w.adicCompletion F) ℂ) (y : v.adicCompletion F) :
    (∏ᶠ w : HeightOneSpectrum (𝓞 F), ψv w (finSingle v y w)) = ψv v y := by
  rw [finprod_eq_single (fun w => ψv w (finSingle v y w)) v]
  · rw [finSingle_apply_self]
  · intro w hw
    rw [finSingle_apply_of_ne v y hw, AddChar.map_zero_eq_one]

theorem diagOne_mul_unipotentGL2 {A : Type*} [CommRing A] (b : Aˣ) (t : A) :
    diagOne b * unipotentGL2 t = unipotentGL2 ((b : A) * t) * diagOne b := by
  apply Units.ext
  ext i j
  simp only [Units.val_mul, diagOne_coe_apply, unipotentGL2_coe, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.diagonal]
  fin_cases i <;> fin_cases j <;> simp

theorem le_exp_of_lt_exp_add_one {x : WithZero (Multiplicative ℤ)} {k : ℤ} (h : x < WithZero.exp (k + 1)) : x ≤ WithZero.exp k := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le'
  · rw [← WithZero.exp_log hx] at h ⊢
    rw [WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

end Ws1.K5a

end

theorem solution
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (β : F) (g : AdelicGL2 (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) = φ g)
    (hsm : IsKfSmooth F φ) :
    ∃ c : HeightOneSpectrum (𝓞 F) → ℤ,
      (∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, c v = 0) ∧
      ∀ b : (AdeleRing (𝓞 F) F)ˣ,
        (∃ v : HeightOneSpectrum (𝓞 F),
          WithZero.exp (c v) < Valued.v (((b : AdeleRing (𝓞 F) F).2) v)) →
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1 (diagOne b) = 0 := by
  classical

  obtain ⟨𝔫, h𝔫, hinv⟩ := AutomorphicForm.IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq hsm

  obtain ⟨ψv, nψ, θr, θc, hlev, hnontriv, hfin, hprod, -, -, -⟩ :=
    AutomorphicForm.exists_localComponents_of_isGlobalAddChar F ψ hψ

  refine ⟨fun v => nψ v - WithZero.log (idealBound (𝓞 F) 𝔫 v), ?_, ?_⟩
  · refine ⟨(hfin.union (finite_setOf_idealBound_ne_one (R := 𝓞 F) h𝔫)).toFinset, fun v hv => ?_⟩
    rw [Set.Finite.mem_toFinset, Set.mem_union, not_or] at hv
    have h1 : nψ v = 0 := by simpa [Function.mem_support] using hv.1
    have h2 : idealBound (𝓞 F) 𝔫 v = 1 := by simpa using hv.2
    show nψ v - WithZero.log (idealBound (𝓞 F) 𝔫 v) = 0
    rw [h1, h2, WithZero.log_one, sub_zero]
  · rintro b ⟨v, hv⟩
    by_contra hW

    have hper : ∀ (g : AdelicGL2 (𝓞 F) F) (β : F) (u : AdeleRing (𝓞 F) F),
        φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * g) = φ (unipotentGL2 u * g) := by
      intro g β u
      rw [unipotentGL2_add, mul_assoc, hleft]

    have key : ∀ y : v.adicCompletion F, Valued.v y ≤ idealBound (𝓞 F) 𝔫 v →
        ψv v (((b : AdeleRing (𝓞 F) F).2 v) * y) = 1 := by
      intro y hy
      set t : AdeleRing (𝓞 F) F := ((0 : InfiniteAdeleRing F), Ws1.K5a.finSingle v y) with htdef
      have ht0 : adeleArch (𝓞 F) F t = 0 := rfl
      have htf : adeleFin (𝓞 F) F t ∈ idealBall (𝓞 F) F 𝔫 := Ws1.K5a.finSingle_mem_idealBall v hy

      have h1 : whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1 (diagOne b * unipotentGL2 t)
          = whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1 (diagOne b) := by
        unfold whittakerCoefficient
        congr 1
        funext x
        congr 1
        have h := hinv (unipotentGL2 x * diagOne b) 1 (by rw [map_one]; exact one_mem _) t ht0 htf
        rw [inv_one, one_mul, mul_one] at h
        rw [← mul_assoc]
        exact h

      have h2 : whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1 (diagOne b * unipotentGL2 t)
          = ψ ((b : AdeleRing (𝓞 F) F) * t) *
            whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1 (diagOne b) := by
        rw [Ws1.K5a.diagOne_mul_unipotentGL2]
        have h := AutomorphicForm.whittakerCoefficient_unipotentGL2_mul F D U gen ψ hψ.principalInvariant φ (diagOne b)
          (fun β u => hper (diagOne b) β u) 1 ((b : AdeleRing (𝓞 F) F) * t)
        rwa [map_one, one_mul] at h
      have h3 : ψ ((b : AdeleRing (𝓞 F) F) * t) = 1 := by
        rw [h1] at h2
        exact (mul_eq_right₀ hW).mp h2.symm

      have hbt : (b : AdeleRing (𝓞 F) F) * t =
          AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
            (Ws1.K5a.finSingle v (((b : AdeleRing (𝓞 F) F).2 v) * y)) := by
        rw [htdef, ← Ws1.K5a.mul_finSingle]
        refine Prod.ext ?_ ?_
        · show (b : AdeleRing (𝓞 F) F).1 * 0 = 0
          exact mul_zero _
        · rfl
      rw [hbt, hprod, Ws1.K5a.finprod_finSingle] at h3
      exact h3

    obtain ⟨x, hxle, hxne⟩ := hnontriv v
    have hb0 : ((b : AdeleRing (𝓞 F) F).2 v) ≠ 0 := by
      intro h0
      have h := congrArg (fun z : AdeleRing (𝓞 F) F => z.2 v) b.mul_inv
      change ((b : AdeleRing (𝓞 F) F).2 v) * ((((b⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2) v)
        = (1 : v.adicCompletion F) at h
      rw [h0, zero_mul] at h
      exact zero_ne_one h
    have hx0 : x ≠ 0 := by
      intro h0
      apply hxne
      rw [h0, AddChar.map_zero_eq_one]
    set y : v.adicCompletion F := ((b : AdeleRing (𝓞 F) F).2 v)⁻¹ * x with hydef
    have hy0 : y ≠ 0 := mul_ne_zero (inv_ne_zero hb0) hx0
    have hy : Valued.v y ≤ idealBound (𝓞 F) 𝔫 v := by
      have hIB := idealBound_ne_zero h𝔫 v
      rw [← WithZero.exp_log hIB]
      apply Ws1.K5a.le_exp_of_lt_exp_add_one

      have hvb : Valued.v ((b : AdeleRing (𝓞 F) F).2 v) ≠ 0 := (Valuation.ne_zero_iff _).mpr hb0
      have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
      have hvy : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy0
      have hmul : Valued.v ((b : AdeleRing (𝓞 F) F).2 v) * Valued.v y = Valued.v x := by
        rw [← map_mul, hydef, mul_inv_cancel_left₀ hb0]
      have hlogmul : WithZero.log (Valued.v ((b : AdeleRing (𝓞 F) F).2 v)) + WithZero.log (Valued.v y)
          = WithZero.log (Valued.v x) := by
        rw [← WithZero.log_mul hvb hvy, hmul]
      have hlogx : WithZero.log (Valued.v x) ≤ nψ v + 1 := by
        rw [← WithZero.exp_log hvx, WithZero.exp_le_exp] at hxle
        exact hxle
      have hlogb : nψ v - WithZero.log (idealBound (𝓞 F) 𝔫 v) < WithZero.log (Valued.v ((b : AdeleRing (𝓞 F) F).2 v)) := by
        rw [← WithZero.exp_log hvb, WithZero.exp_lt_exp] at hv
        exact hv
      rw [← WithZero.exp_log hvy, WithZero.exp_lt_exp]
      omega
    have h := key y hy
    rw [hydef, mul_inv_cancel_left₀ hb0] at h
    exact hxne h

end S_AutomorphicForm_exists_whittakerCoefficient_one_diagOne_eq_zero_of_exp_lt_valuation
end P2MW
export P2MW.S_AutomorphicForm_exists_whittakerCoefficient_one_diagOne_eq_zero_of_exp_lt_valuation (solution)
