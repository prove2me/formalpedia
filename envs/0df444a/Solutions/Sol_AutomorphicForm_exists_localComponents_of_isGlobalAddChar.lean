-- Prove2me | solution 1 for AutomorphicForm.exists_localComponents_of_isGlobalAddChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/77ab2efc-a69a-50f9-a321-ca14a9ee4c94

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicTraceFin
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.RingTheory.Complex
import Theorems.Thm_AutomorphicForm_exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_count_differentIdeal
import Theorems.Thm_NumberField_StandardAddChar_stdAddChar_apply_mk_zero_eq_fourierChar_trace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_localComponents_of_isGlobalAddChar
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

noncomputable section

section FiniteProduct

p2m_open "NumberField P2MW.S_AutomorphicForm_exists_localComponents_of_isGlobalAddChar.NumberField NumberField.StandardAddChar P2MW.S_AutomorphicForm_exists_localComponents_of_isGlobalAddChar.NumberField.StandardAddChar IsDedekindDomain"

namespace StdAddCharFinprod

variable (F : Type) [Field F] [NumberField F]

private def finPart : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ :=
  (stdAddChar F).compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

private theorem finPart_finAdeleSingleAt (v : HeightOneSpectrum (𝓞 F)) (z : v.adicCompletion F) :
    finPart F (finAdeleSingleAt F v z) = psiLocal F v z := rfl

private def evalHom (w : HeightOneSpectrum (𝓞 F)) : FiniteAdeleRing (𝓞 F) F →+ w.adicCompletion F where
  toFun a := a w
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem evalHom_apply (w : HeightOneSpectrum (𝓞 F)) (a : FiniteAdeleRing (𝓞 F) F) :
    evalHom F w a = a w := rfl

private theorem structureMap_mem {ι : Type*} {R : ι → Type*} {A : (i : ι) → Set (R i)} {𝓕 : Filter ι}
    (z : (i : ι) → A i) (i : ι) : RestrictedProduct.structureMap R A 𝓕 z i ∈ A i :=
  (z i).2

private theorem finPart_eq_psiFin_traceFinHom (y : FiniteAdeleRing (𝓞 F) F) :
    finPart F y = psiFin (traceFinHom F y) := by
  have h : finPart F y
      = psiArch ((adelicTraceData F).traceInf 0) * psiFin ((adelicTraceData F).traceFin y) := rfl
  rw [h, map_zero, AddChar.map_zero_eq_one, one_mul]
  rfl

private theorem finPart_eq_one_of_forall_mem (y : FiniteAdeleRing (𝓞 F) F)
    (hy : ∀ v : HeightOneSpectrum (𝓞 F), y v ∈ v.adicCompletionIntegers F) : finPart F y = 1 := by
  let w : Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F := fun v => ⟨y v, hy v⟩
  have hw : (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite w :
        FiniteAdeleRing (𝓞 F) F) = y :=
    FiniteAdeleRing.ext F fun _ => rfl
  rw [finPart_eq_psiFin_traceFinHom, ← hw, traceFinHom_structureMap]
  exact psiFin_eq_one_of_forall_mem _ fun p => structureMap_mem _ p

private theorem finPart_sum {ι : Type*} (s : Finset ι) (f : ι → FiniteAdeleRing (𝓞 F) F) :
    finPart F (∑ i ∈ s, f i) = ∏ i ∈ s, finPart F (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty, Finset.prod_empty, AddChar.map_zero_eq_one]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

private theorem sum_finAdeleSingleAt_apply (x : FiniteAdeleRing (𝓞 F) F)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 F)) :
    (∑ v ∈ S, finAdeleSingleAt F v (x v)) w = ∑ v ∈ S, finAdeleSingleAt F v (x v) w := by
  rw [← evalHom_apply, map_sum]
  rfl

end StdAddCharFinprod

namespace NumberField p2m_export "NumberField" "InfiniteAdeleRing InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp mixedEmbedding.mixedEmbedding_apply_isComplex place InfinitePlace.embedding_of_isReal mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace mixedEmbedding.mixedEmbedding_apply_isReal InfinitePlace AdeleRing" namespace StandardAddChar p2m_export "NumberField.StandardAddChar" "finAdeleSingleAt finAdeleSingleAt_apply_self finAdeleSingleAt_apply_of_ne psiLocal traceFinHom traceFinHom_structureMap adelicTraceData stdAddChar psiFin psiFin_eq_one_of_forall_mem psiArch stdAddChar_apply_mk_zero_eq_fourierChar_trace" end NumberField.StandardAddChar
p2m_open_scoped "NumberField NumberField.StandardAddChar" in
open StdAddCharFinprod in

private theorem NumberField.StandardAddChar.stdAddChar_mk_zero_eq_finprod_psiLocal
    (F : Type) [Field F] [NumberField F] (x : FiniteAdeleRing (𝓞 F) F) :
    stdAddChar F ((0 : InfiniteAdeleRing F), x) = ∏ᶠ v : HeightOneSpectrum (𝓞 F), psiLocal F v (x v) := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | x v ∉ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.mp x.eventually
  have hS : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ hfin.toFinset → x v ∈ v.adicCompletionIntegers F := by
    intro v hv
    by_contra h
    exact hv (hfin.mem_toFinset.mpr h)
  obtain ⟨y, hy⟩ : ∃ y : FiniteAdeleRing (𝓞 F) F,
      y = x - ∑ v ∈ hfin.toFinset, finAdeleSingleAt F v (x v) := ⟨_, rfl⟩
  have hy_int : ∀ w : HeightOneSpectrum (𝓞 F), y w ∈ w.adicCompletionIntegers F := by
    intro w
    have hyw : y w = x w - ∑ v ∈ hfin.toFinset, finAdeleSingleAt F v (x v) w := by
      rw [hy, ← sum_finAdeleSingleAt_apply]
      exact map_sub (evalHom F w) _ _
    by_cases hw : w ∈ hfin.toFinset
    · have h1 : ∑ v ∈ hfin.toFinset, finAdeleSingleAt F v (x v) w = x w := by
        rw [Finset.sum_eq_single_of_mem w hw
          (fun v _ hvw => finAdeleSingleAt_apply_of_ne F v (x v) (Ne.symm hvw))]
        exact finAdeleSingleAt_apply_self F w (x w)
      rw [hyw, h1, sub_self]
      exact zero_mem _
    · have h1 : ∑ v ∈ hfin.toFinset, finAdeleSingleAt F v (x v) w = 0 :=
        Finset.sum_eq_zero fun v hv =>
          finAdeleSingleAt_apply_of_ne F v (x v) fun hwv => hw (by rw [hwv]; exact hv)
      rw [hyw, h1, sub_zero]
      exact hS w hw
  have hx : x = y + ∑ v ∈ hfin.toFinset, finAdeleSingleAt F v (x v) := by
    rw [hy, sub_add_cancel]
  have hprod : finPart F x = ∏ v ∈ hfin.toFinset, psiLocal F v (x v) := by
    conv_lhs => rw [hx]
    rw [AddChar.map_add_eq_mul, finPart_eq_one_of_forall_mem F y hy_int, one_mul, finPart_sum]
    rfl
  have hsupp : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => psiLocal F v (x v))
      ⊆ ↑hfin.toFinset := by
    intro v hv
    rw [Function.mem_mulSupport] at hv
    by_contra hvS
    apply hv
    rw [← finPart_finAdeleSingleAt]
    refine finPart_eq_one_of_forall_mem F _ fun w => ?_
    by_cases hwv : w = v
    · rw [hwv, finAdeleSingleAt_apply_self]
      exact hS v hvS
    · rw [finAdeleSingleAt_apply_of_ne F v (x v) hwv]
      exact zero_mem _
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
  exact hprod

end FiniteProduct

section TwistedLevels

p2m_open "NumberField P2MW.S_AutomorphicForm_exists_localComponents_of_isGlobalAddChar.NumberField IsDedekindDomain"
open scoped nonZeroDivisors

namespace LanglandsTunnell p2m_export "LanglandsTunnell" "TateLocal.addCharLevel TateLocal.psiLocal_ne_one TateLocal.psiLocal_eq_one_of_mem_integers TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal" namespace TateLocal p2m_export "LanglandsTunnell.TateLocal" "addCharLevel psiLocal_ne_one psiLocal_eq_one_of_mem_integers addCharLevel_psiLocal_eq_count_differentIdeal" end LanglandsTunnell.TateLocal
p2m_open_scoped "LanglandsTunnell LanglandsTunnell.TateLocal" in

private theorem LanglandsTunnell.TateLocal.addCharLevel_spec {K : Type} [Field K] [NumberField K]
    {v : HeightOneSpectrum (𝓞 K)} (χ : AddChar (v.adicCompletion K) ℂ) (hχ : χ ≠ 1) (m : ℤ)
    (hm : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp m → χ x = 1) :
    (∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (addCharLevel χ) → χ x = 1) ∧
      ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (addCharLevel χ + 1) ∧ χ x ≠ 1 := by
  obtain ⟨x₀, hx₀⟩ := AddChar.ne_one_iff.mp hχ
  have hx₀0 : x₀ ≠ 0 := by
    rintro rfl
    exact hx₀ (AddChar.map_zero_eq_one χ)
  have hvx₀ : Valued.v x₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hx₀0
  have hub : ∀ n ∈ {n : ℤ | ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → χ x = 1},
      n ≤ WithZero.log (Valued.v x₀) - 1 := by
    intro n hn
    by_contra hlt
    push Not at hlt
    refine hx₀ (hn x₀ ?_)
    rw [← WithZero.exp_log hvx₀]
    exact WithZero.exp_le_exp.mpr (by omega)
  have hmem : addCharLevel χ ∈
      {n : ℤ | ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → χ x = 1} :=
    Int.csSup_mem ⟨m, hm⟩ ⟨WithZero.log (Valued.v x₀) - 1, hub⟩
  have hnot : ¬ ∀ x : v.adicCompletion K,
      Valued.v x ≤ WithZero.exp (addCharLevel χ + 1) → χ x = 1 := by
    intro hmem1
    have h1 : addCharLevel χ + 1 ≤ addCharLevel χ :=
      le_csSup ⟨WithZero.log (Valued.v x₀) - 1, hub⟩ hmem1
    omega
  push Not at hnot
  exact ⟨hmem, hnot⟩

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.TateLocal" in

private theorem LanglandsTunnell.TateLocal.addCharLevel_eq_of_ball {K : Type} [Field K] [NumberField K]
    {v : HeightOneSpectrum (𝓞 K)} (χ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (h1 : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → χ x = 1)
    (h2 : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ χ x ≠ 1) :
    addCharLevel χ = n := by
  obtain ⟨x₁, hx₁le, hx₁ne⟩ := h2
  have hn : n ∈ {k : ℤ | ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp k → χ x = 1} := h1
  have hub : ∀ k ∈ {k : ℤ | ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp k → χ x = 1},
      k ≤ n := by
    intro k hk
    by_contra hnk
    push Not at hnk
    exact hx₁ne (hk x₁ (hx₁le.trans (WithZero.exp_le_exp.mpr (by omega))))
  exact le_antisymm (csSup_le ⟨n, hn⟩ hub) (le_csSup ⟨n, hub⟩ hn)

p2m_open_scoped "NumberField NumberField.StandardAddChar" in

private theorem NumberField.StandardAddChar.exists_twistedComponents
    (F : Type) [Field F] [NumberField F] (a : F) (ha : a ≠ 0) :
    ∃ (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ)
      (nψ : HeightOneSpectrum (𝓞 F) → ℤ),
      (∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
        Valued.v x ≤ WithZero.exp (nψ v) → ψv v x = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 F),
        ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (nψ v + 1) ∧ ψv v x ≠ 1) ∧
      (Function.support nψ).Finite ∧
      (∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
        ψv v x = psiLocal F v (algebraMap F (v.adicCompletion F) a * x)) := by
  classical
  have hval : ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (algebraMap F (v.adicCompletion F) a) = v.valuation F a := fun v =>
    v.valuedAdicCompletion_eq_valuation' a
  have hvne : ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (algebraMap F (v.adicCompletion F) a) ≠ 0 := by
    intro v
    rw [hval v]
    exact (Valuation.ne_zero_iff _).mpr ha
  have hane : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) a ≠ 0 :=
    fun v => (Valuation.ne_zero_iff Valued.v).mp (hvne v)
  have happly : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
      (psiLocal F v).compAddMonoidHom
          (AddMonoidHom.mulLeft (algebraMap F (v.adicCompletion F) a)) x
        = psiLocal F v (algebraMap F (v.adicCompletion F) a * x) := fun v x => rfl
  have hball : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
      Valued.v x ≤ WithZero.exp (-WithZero.log (Valued.v (algebraMap F (v.adicCompletion F) a))) →
      (psiLocal F v).compAddMonoidHom
        (AddMonoidHom.mulLeft (algebraMap F (v.adicCompletion F) a)) x = 1 := by
    intro v x hx
    rw [happly v x]
    apply LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers F v
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul]
    calc Valued.v (algebraMap F (v.adicCompletion F) a) * Valued.v x
        ≤ Valued.v (algebraMap F (v.adicCompletion F) a) *
          WithZero.exp (-WithZero.log (Valued.v (algebraMap F (v.adicCompletion F) a))) :=
          mul_le_mul_right hx _
      _ = 1 := by
          rw [WithZero.exp_neg, WithZero.exp_log (hvne v)]
          exact mul_inv_cancel₀ (hvne v)
  have hne1 : ∀ v : HeightOneSpectrum (𝓞 F),
      (psiLocal F v).compAddMonoidHom
        (AddMonoidHom.mulLeft (algebraMap F (v.adicCompletion F) a)) ≠ 1 := by
    intro v h1
    apply LanglandsTunnell.TateLocal.psiLocal_ne_one F v
    refine AddChar.ext _ _ fun y => ?_
    rw [AddChar.one_apply]
    have hy := DFunLike.congr_fun h1 ((algebraMap F (v.adicCompletion F) a)⁻¹ * y)
    rw [happly, AddChar.one_apply, mul_inv_cancel_left₀ (hane v)] at hy
    exact hy
  have hspec := fun v : HeightOneSpectrum (𝓞 F) =>
    LanglandsTunnell.TateLocal.addCharLevel_spec
      ((psiLocal F v).compAddMonoidHom
        (AddMonoidHom.mulLeft (algebraMap F (v.adicCompletion F) a)))
      (hne1 v) _ (hball v)
  refine ⟨fun v => (psiLocal F v).compAddMonoidHom
      (AddMonoidHom.mulLeft (algebraMap F (v.adicCompletion F) a)),
    fun v => LanglandsTunnell.TateLocal.addCharLevel ((psiLocal F v).compAddMonoidHom
      (AddMonoidHom.mulLeft (algebraMap F (v.adicCompletion F) a))), ?_, ?_, ?_, ?_⟩
  · exact fun v => (hspec v).1
  · exact fun v => (hspec v).2
  · have hfin1 : {v : HeightOneSpectrum (𝓞 F) |
        FractionalIdeal.count F v (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0}.Finite := by
      have h := FractionalIdeal.finite_factors (K := F)
        (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)
      rw [Filter.eventually_cofinite] at h
      exact h
    have hfin2 : {v : HeightOneSpectrum (𝓞 F) | v.valuation F a ≠ 1}.Finite := by
      refine Set.Finite.subset ((IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 F) a).union
        (IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 F) a⁻¹)) ?_
      intro v hv
      have hv' : v.valuation F a ≠ 1 := hv
      rcases lt_or_gt_of_ne hv' with hlt | hgt
      · refine Set.mem_union_right _ ?_
        show 1 < v.valuation F a⁻¹
        rw [map_inv₀]
        exact (one_lt_inv₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr ha))).mpr hlt
      · exact Set.mem_union_left _ hgt
    refine Set.Finite.subset (hfin1.union hfin2) ?_
    intro v hv
    simp only [Function.mem_support] at hv
    by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hnot
    obtain ⟨hc0, hu1⟩ := hnot
    apply hv
    have hvu : Valued.v (algebraMap F (v.adicCompletion F) a) = 1 := by
      rw [hval v]; exact hu1
    have hsets : {n : ℤ | ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n →
          (psiLocal F v).compAddMonoidHom
            (AddMonoidHom.mulLeft (algebraMap F (v.adicCompletion F) a)) x = 1}
        = {n : ℤ | ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n →
            psiLocal F v x = 1} := by
      ext n
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h x hx
        have hx' : Valued.v ((algebraMap F (v.adicCompletion F) a)⁻¹ * x) ≤ WithZero.exp n := by
          rwa [map_mul, map_inv₀, hvu, inv_one, one_mul]
        have h2 := h _ hx'
        rwa [happly, mul_inv_cancel_left₀ (hane v)] at h2
      · intro h x hx
        rw [happly]
        refine h _ ?_
        rwa [map_mul, hvu, one_mul]
    have h3 : LanglandsTunnell.TateLocal.addCharLevel
          ((psiLocal F v).compAddMonoidHom
            (AddMonoidHom.mulLeft (algebraMap F (v.adicCompletion F) a)))
        = LanglandsTunnell.TateLocal.addCharLevel (psiLocal F v) := congrArg sSup hsets
    rw [h3, LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal F v]
    exact hc0
  · exact fun v x => rfl

end TwistedLevels

section Archimedean

p2m_open "NumberField P2MW.S_AutomorphicForm_exists_localComponents_of_isGlobalAddChar.NumberField NumberField.StandardAddChar P2MW.S_AutomorphicForm_exists_localComponents_of_isGlobalAddChar.NumberField.StandardAddChar IsDedekindDomain"

section PiTrace

namespace Algebra p2m_export "Algebra" "trace_eq_matrix_trace trace algebraMap trace_complex_apply trace_trace trace_prod_apply leftMulMatrix leftMulMatrix_eq_repr_mul" end Algebra
p2m_open_scoped "Algebra" in

private theorem Algebra.trace_pi_self {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (f : ι → R) : Algebra.trace R (ι → R) f = ∑ i, f i := by
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun R ι),
    show Algebra.leftMulMatrix (Pi.basisFun R ι) f = Matrix.diagonal f from ?_,
    Matrix.trace_diagonal]
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Pi.basisFun_apply, Pi.basisFun_repr,
    Pi.mul_apply, Pi.single_apply, Matrix.diagonal_apply, mul_ite, mul_one, mul_zero]

p2m_open_scoped "Algebra" in

private theorem Algebra.trace_pi_complex {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → ℂ) :
    Algebra.trace ℝ (ι → ℂ) g = ∑ w, 2 * (g w).re := by
  rw [← Algebra.trace_trace (S := ℂ), Algebra.trace_pi_self, map_sum]
  exact Finset.sum_congr rfl fun w _ => Algebra.trace_complex_apply (g w)

end PiTrace

p2m_open_scoped "NumberField NumberField.StandardAddChar" in

private theorem NumberField.StandardAddChar.exists_arch_frequencies (F : Type) [Field F] [NumberField F]
    (a : F) (ha : a ≠ 0) :
    ∃ (θr : {w : InfinitePlace F // w.IsReal} → ℝ) (θc : {w : InfinitePlace F // w.IsComplex} → ℂ),
      (∀ i, θr i ≠ 0) ∧ (∀ w, θc w ≠ 0) ∧
      ∀ p : mixedEmbedding.mixedSpace F,
        stdAddChar F (algebraMap F (InfiniteAdeleRing F) a
            * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm p, 0)
          = (∏ᶠ i : {w : InfinitePlace F // w.IsReal},
                Complex.exp (-(((2 * Real.pi * θr i * p.1 i : ℝ) : ℂ) * Complex.I)))
            * ∏ᶠ w : {w : InfinitePlace F // w.IsComplex},
                Complex.exp (-(((4 * Real.pi * (θc w * p.2 w).re : ℝ) : ℂ) * Complex.I)) := by
  classical

  refine ⟨fun i => -(NumberField.mixedEmbedding F a).1 i,
    fun w => -(NumberField.mixedEmbedding F a).2 w, ?_, ?_, ?_⟩
  ·
    intro i
    rw [neg_ne_zero, mixedEmbedding.mixedEmbedding_apply_isReal]
    exact fun h => ha ((map_eq_zero (InfinitePlace.embedding_of_isReal i.2)).mp h)
  ·
    intro w
    rw [neg_ne_zero, mixedEmbedding.mixedEmbedding_apply_isComplex]
    exact (map_ne_zero w.1.embedding).mpr ha
  · intro p

    rw [stdAddChar_apply_mk_zero_eq_fourierChar_trace]

    rw [map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F),
      ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp,
      RingEquiv.apply_symm_apply]

    rw [show Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (mixedEmbedding F a * p)
          = (∑ i : {w : InfinitePlace F // w.IsReal}, (mixedEmbedding F a).1 i * p.1 i)
            + ∑ w : {w : InfinitePlace F // w.IsComplex},
              2 * ((mixedEmbedding F a).2 w * p.2 w).re from ?_]
    swap
    · rw [Algebra.trace_prod_apply, Algebra.trace_pi_self, Algebra.trace_pi_complex,
        Prod.fst_mul, Prod.snd_mul]
      rfl

    rw [Real.fourierChar_apply]
    simp only [neg_mul, Complex.neg_re, mul_neg, Complex.ofReal_neg, neg_neg,
      finprod_eq_prod_of_fintype, ← Complex.exp_sum, ← Finset.sum_mul, ← Complex.ofReal_sum,
      ← Complex.exp_add, ← add_mul, ← Complex.ofReal_add]
    refine congrArg Complex.exp (congrArg (· * Complex.I) (congrArg Complex.ofReal ?_))
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun _ _ => by ring)
      (Finset.sum_congr rfl fun _ _ => by ring)

end Archimedean

section Assembly

p2m_open "NumberField P2MW.S_AutomorphicForm_exists_localComponents_of_isGlobalAddChar.NumberField NumberField.StandardAddChar P2MW.S_AutomorphicForm_exists_localComponents_of_isGlobalAddChar.NumberField.StandardAddChar IsDedekindDomain AutomorphicForm"

theorem solution
    (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ) :
    ∃ (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ) (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
      (θr : {w : InfinitePlace F // w.IsReal} → ℝ) (θc : {w : InfinitePlace F // w.IsComplex} → ℂ),
      (∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
        Valued.v x ≤ WithZero.exp (nψ v) → ψv v x = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 F),
        ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (nψ v + 1) ∧ ψv v x ≠ 1) ∧
      (Function.support nψ).Finite ∧
      (∀ x : FiniteAdeleRing (𝓞 F) F,
        ψ (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) x)
          = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ψv v (x v)) ∧
      (∀ i, θr i ≠ 0) ∧ (∀ w, θc w ≠ 0) ∧
      (∀ p : mixedEmbedding.mixedSpace F,
        ψ (AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm p))
          = (∏ᶠ i : {w : InfinitePlace F // w.IsReal},
                Complex.exp (-(((2 * Real.pi * θr i * p.1 i : ℝ) : ℂ) * Complex.I)))
            * ∏ᶠ w : {w : InfinitePlace F // w.IsComplex},
                Complex.exp (-(((4 * Real.pi * (θc w * p.2 w).re : ℝ) : ℂ) * Complex.I))) := by
  obtain ⟨a, ha, hψa⟩ := AutomorphicForm.exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar F hψ
  obtain ⟨ψv, nψ, h1, h2, h3, hhandle⟩ := NumberField.StandardAddChar.exists_twistedComponents F a ha
  obtain ⟨θr, θc, hθr, hθc, harch⟩ := NumberField.StandardAddChar.exists_arch_frequencies F a ha
  refine ⟨ψv, nψ, θr, θc, h1, h2, h3, ?_, hθr, hθc, ?_⟩
  · intro x
    have hmul : (fun y : AdeleRing (𝓞 F) F => algebraMap F (AdeleRing (𝓞 F) F) a * y)
          (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) x)
        = ((0 : InfiniteAdeleRing F), algebraMap F (FiniteAdeleRing (𝓞 F) F) a * x) :=
      Prod.ext (mul_zero (algebraMap F (InfiniteAdeleRing F) a)) rfl
    beta_reduce at hmul
    rw [hψa, hmul, NumberField.StandardAddChar.stdAddChar_mk_zero_eq_finprod_psiLocal]
    refine finprod_congr fun v => ?_
    rw [hhandle]
    rfl
  · intro p
    have hmul : (fun y : AdeleRing (𝓞 F) F => algebraMap F (AdeleRing (𝓞 F) F) a * y)
          (AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm p))
        = (algebraMap F (InfiniteAdeleRing F) a * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm p,
            (0 : FiniteAdeleRing (𝓞 F) F)) :=
      Prod.ext rfl (mul_zero (algebraMap F (FiniteAdeleRing (𝓞 F) F) a))
    beta_reduce at hmul
    rw [hψa, hmul, harch]

end Assembly

end

end S_AutomorphicForm_exists_localComponents_of_isGlobalAddChar
end P2MW
export P2MW.S_AutomorphicForm_exists_localComponents_of_isGlobalAddChar (solution)
