-- Prove2me | solution 1 for AutomorphicForm.WhittakerModel.exists_torusShell_eq_zero_and_torusShell_dual_eq_stdRootNumberAt_mul_of_mem_localLevelOne_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ffb1f693-4eda-5cb5-bb69-8c849e2731ba

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_setIntegral_addChar_mul_charExt_eq_zero_of_valued_ne
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_finset_hasConductorExponentAt_le_eq_sum_of_forall_mem_higherUnitsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_forall_mem_higherUnitsAt_apply_eq_psiLocal_mul_sub_one_of_hasConductorExponentAt
import Theorems.Thm_LanglandsTunnell_TateLocal_setIntegral_addChar_mul_mul_charExt_eq_apply_mul_setIntegral_of_forall_mem_higherUnitsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_setIntegral_psiLocal_mul_charExt_inv_mul_cpow_eq_charExt_mul_stdRootNumberAt
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_stdRootNumberAt_inv_eq_apply_neg_one
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_ne_zero_of_hasConductorExponentAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_WhittakerModel_exists_torusShell_eq_zero_and_torusShell_dual_eq_stdRootNumberAt_mul_of_mem_localLevelOne_top
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker NumberField.AdelicLevel NumberField.StandardAddChar Topology

open scoped NNReal ENNReal

namespace AutomorphicForm
namespace WhittakerModel
namespace TorusShellCore
p2m_open "AutomorphicForm"

section GLtwo

variable {F : Type*} [Field F]

def gl2 (a b c d : F) (h : a * d - b * c ≠ 0) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; c, d] (by rwa [Matrix.det_fin_two_of])

@[scoped simp] theorem gl2_coe (a b c d : F) (h : a * d - b * c ≠ 0) :
    ((gl2 a b c d h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] := rfl

def lowerUni (x : F) : GL (Fin 2) F := gl2 1 0 x 1 (by simp)

def weylJ : GL (Fin 2) F := gl2 0 1 (-1) 0 (by simp)

theorem lowerUni_coe (x : F) : ((lowerUni x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; x, 1] := rfl

theorem weylJ_coe : ((weylJ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl

theorem unipotent_coe (x : F) :
    ((UnramifiedWhittaker.unipotent x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, x; 0, 1] := rfl

theorem diagOne_coe (a : Fˣ) :
    ((AdelicLevel.diagOne a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![(a : F), 0; 0, 1] := by
  ext i j
  rw [AdelicLevel.diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem scalar_coe (z : Fˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      = !![(z : F), 0; 0, (z : F)] := by
  ext i j
  change (Matrix.scalar (Fin 2) (z : F)) i j = _
  fin_cases i <;> fin_cases j <;> simp

theorem gl_eq_of_entries {g h : GL (Fin 2) F}
    (h00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = (h : Matrix (Fin 2) (Fin 2) F) 0 0)
    (h01 : (g : Matrix (Fin 2) (Fin 2) F) 0 1 = (h : Matrix (Fin 2) (Fin 2) F) 0 1)
    (h10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = (h : Matrix (Fin 2) (Fin 2) F) 1 0)
    (h11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = (h : Matrix (Fin 2) (Fin 2) F) 1 1) : g = h := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem mul_coe_apply (g h : GL (Fin 2) F) (i j : Fin 2) :
    ((g * h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j
      = (g : Matrix (Fin 2) (Fin 2) F) i 0 * (h : Matrix (Fin 2) (Fin 2) F) 0 j
        + (g : Matrix (Fin 2) (Fin 2) F) i 1 * (h : Matrix (Fin 2) (Fin 2) F) 1 j := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem eq_weylJ_of_coe {w : GL (Fin 2) F} (hw : (w : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0]) :
    w = weylJ := by
  apply gl_eq_of_entries <;> simp [hw, weylJ_coe]

theorem unipotent_mul (x y : F) :
    (UnramifiedWhittaker.unipotent x : GL (Fin 2) F) * UnramifiedWhittaker.unipotent y =
      UnramifiedWhittaker.unipotent (x + y) := by
  apply gl_eq_of_entries <;> simp [mul_coe_apply, unipotent_coe] <;> ring

theorem unipotent_zero : (UnramifiedWhittaker.unipotent (0 : F) : GL (Fin 2) F) = 1 := by
  apply gl_eq_of_entries <;> simp [unipotent_coe]

theorem unipotent_inv (x : F) :
    (UnramifiedWhittaker.unipotent x : GL (Fin 2) F)⁻¹ = UnramifiedWhittaker.unipotent (-x) := by
  rw [inv_eq_iff_mul_eq_one, unipotent_mul, add_neg_cancel, unipotent_zero]

theorem lowerUni_mul (x y : F) : (lowerUni x : GL (Fin 2) F) * lowerUni y = lowerUni (x + y) := by
  apply gl_eq_of_entries <;> simp [mul_coe_apply, lowerUni_coe] <;> ring

theorem lowerUni_zero : (lowerUni (0 : F) : GL (Fin 2) F) = 1 := by
  apply gl_eq_of_entries <;> simp [lowerUni_coe]

theorem lowerUni_inv (x : F) : (lowerUni x : GL (Fin 2) F)⁻¹ = lowerUni (-x) := by
  rw [inv_eq_iff_mul_eq_one, lowerUni_mul, add_neg_cancel, lowerUni_zero]

theorem scalar_mul_comm (z : Fˣ) (g : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) z * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) z := by
  apply gl_eq_of_entries <;> simp [mul_coe_apply, scalar_coe] <;> ring

theorem diagOne_mul_unipotent (u : Fˣ) (x : F) :
    (AdelicLevel.diagOne u : GL (Fin 2) F) * UnramifiedWhittaker.unipotent x =
      UnramifiedWhittaker.unipotent ((u : F) * x) * AdelicLevel.diagOne u := by
  apply gl_eq_of_entries <;> simp [mul_coe_apply, unipotent_coe, diagOne_coe]

theorem weylJ_mul_unipotent_eq (x : Fˣ) :
    (weylJ : GL (Fin 2) F) * UnramifiedWhittaker.unipotent (x : F) =
      UnramifiedWhittaker.unipotent (-((x⁻¹ : Fˣ) : F)) * Matrix.GeneralLinearGroup.scalar (Fin 2) (-x) *
        AdelicLevel.diagOne (x⁻¹ ^ 2) * lowerUni ((x⁻¹ : Fˣ) : F) := by
  have hx : (x : F) ≠ 0 := x.ne_zero
  obtain ⟨d, hd⟩ : ∃ d : Fˣ, d = x⁻¹ ^ 2 := ⟨_, rfl⟩
  have hdv : (d : F) = (x : F)⁻¹ ^ 2 := by rw [hd]; simp
  rw [← hd]
  apply gl_eq_of_entries <;>
    simp [mul_coe_apply, unipotent_coe, lowerUni_coe, weylJ_coe, diagOne_coe, scalar_coe, hdv] <;>
    field_simp <;> ring

theorem diagOne_mul_weylJ_mul_unipotent (y x : Fˣ) :
    (AdelicLevel.diagOne y : GL (Fin 2) F) * weylJ * UnramifiedWhittaker.unipotent (x : F) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (-x) *
        UnramifiedWhittaker.unipotent ((y : F) * -((x⁻¹ : Fˣ) : F)) *
          AdelicLevel.diagOne (y * x⁻¹ ^ 2) * lowerUni ((x⁻¹ : Fˣ) : F) := by
  have hx : (x : F) ≠ 0 := x.ne_zero
  obtain ⟨d, hd⟩ : ∃ d : Fˣ, d = y * x⁻¹ ^ 2 := ⟨_, rfl⟩
  have hdv : (d : F) = (y : F) * (x : F)⁻¹ ^ 2 := by rw [hd]; simp
  rw [← hd]
  apply gl_eq_of_entries <;>
    simp [mul_coe_apply, unipotent_coe, lowerUni_coe, weylJ_coe, diagOne_coe, scalar_coe, hdv] <;>
    field_simp <;> ring

theorem diagOne_mul_lowerUni (u : Fˣ) (e : F) :
    (AdelicLevel.diagOne u : GL (Fin 2) F) * lowerUni e
      = lowerUni (e * ((u⁻¹ : Fˣ) : F)) * AdelicLevel.diagOne u := by
  apply gl_eq_of_entries <;>
    simp [mul_coe_apply, lowerUni_coe, diagOne_coe, -map_inv, Units.val_inv_eq_inv_val]

end GLtwo

section Level

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem pow_asIdeal_ne_bot (c : ℕ) : v.asIdeal ^ c ≠ ⊥ := pow_ne_zero c v.ne_bot

theorem idealBound_pow (c : ℕ) :
    AdelicLevel.idealBound (𝓞 K) (v.asIdeal ^ c) v = WithZero.exp (-(c : ℤ)) := by
  classical
  rw [AdelicLevel.idealBound_of_ne_bot (pow_asIdeal_ne_bot K v c), Associates.mk_pow,
    Associates.count_pow (Associates.mk_ne_zero.mpr v.ne_bot) (Associates.irreducible_mk.mpr v.irreducible),
    Associates.count_self (Associates.irreducible_mk.mpr v.irreducible), mul_one]

theorem inv_mem_higherUnitsAt {n : ℕ} {u : (v.adicCompletion K)ˣ} (hu : u ∈ higherUnitsAt K v n) :
    u⁻¹ ∈ higherUnitsAt K v n := by
  obtain ⟨hval, hball⟩ := hu
  have hval' : Valued.v ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hval, inv_one]
  refine ⟨hval', ?_⟩
  rcases hball with h0 | hle
  · exact Or.inl h0
  · right
    have : ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1
        = -(((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) * ((u : v.adicCompletion K) - 1)) := by
      rw [mul_sub, mul_one, Units.inv_mul, neg_sub]
    rw [this, Valuation.map_neg, Valuation.map_mul, hval', one_mul]
    exact hle

theorem valued_sub_one_le_of_mem_higherUnitsAt {c : ℕ} {u : (v.adicCompletion K)ˣ}
    (hu : u ∈ higherUnitsAt K v c) :
    Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp (-(c : ℤ)) := by
  obtain ⟨hval, hball⟩ := hu
  rcases hball with h0 | hle
  · subst h0
    simp only [CharP.cast_eq_zero, neg_zero, WithZero.exp_zero]
    refine le_trans (Valuation.map_sub _ _ _) (max_le (le_of_eq hval) ?_)
    rw [Valuation.map_one]
  · exact hle

theorem valued_add_le {x y : v.adicCompletion K} {γ : WithZero (Multiplicative ℤ)} (hx : Valued.v x ≤ γ)
    (hy : Valued.v y ≤ γ) : Valued.v (x + y) ≤ γ :=
  (Valuation.map_add _ _ _).trans (max_le hx hy)

theorem entries_mul_le {M N : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)} {α β : WithZero (Multiplicative ℤ)}
    (hM : ∀ i j, Valued.v (M i j) ≤ α) (hN : ∀ i j, Valued.v (N i j) ≤ β) (i j : Fin 2) :
    Valued.v ((M * N) i j) ≤ α * β := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine valued_add_le K v ?_ ?_ <;> rw [Valuation.map_mul] <;> exact mul_le_mul' (hM _ _) (hN _ _)

theorem isLocalLevelOne_top_iff (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :
    AdelicDock.IsLocalLevelOne (𝓞 K) K v ⊤ m ↔ ∀ i j, Valued.v (m i j) ≤ 1 := by
  constructor
  · intro h i j
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h.integral i j)
  · intro h
    refine ⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (h i j), ?_, ?_⟩
    · rw [AdelicLevel.idealBound_top]; exact h 1 0
    · rw [AdelicLevel.idealBound_top]
      exact (Valuation.map_sub _ _ _).trans (max_le (h 1 1) (by rw [Valuation.map_one]))

theorem mem_localLevelOne_top_iff (k : GL (Fin 2) (v.adicCompletion K)) :
    k ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤ ↔
      (∀ i j, Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ 1) ∧
        ∀ i j, Valued.v (((k⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
          i j) ≤ 1 := by
  rw [AdelicDock.mem_localLevelOne_iff, isLocalLevelOne_top_iff, isLocalLevelOne_top_iff]

def IsCongMat (c : ℕ) (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) : Prop :=
  ∀ i j, Valued.v ((m - 1) i j) ≤ WithZero.exp (-(c : ℤ))

variable {K v}

theorem mem_localLevelOne_pow_of_isCongMat {c : ℕ} {g : GL (Fin 2) (v.adicCompletion K)}
    (hg : g ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤) (hc : IsCongMat K v c (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) :
    g ∈ AdelicDock.localLevelOne (𝓞 K) K v (v.asIdeal ^ c) := by
  rw [mem_localLevelOne_top_iff] at hg
  obtain ⟨hint, hint'⟩ := hg

  have hc' : IsCongMat K v c ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
    intro i j
    have hmat : ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1
        = -(((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) * ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1)) := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one, neg_sub]
    rw [hmat, Matrix.neg_apply, Valuation.map_neg]
    have := entries_mul_le K v hint' hc i j
    rwa [one_mul] at this
  have key : ∀ m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), (∀ i j, Valued.v (m i j) ≤ 1) →
      IsCongMat K v c m → AdelicDock.IsLocalLevelOne (𝓞 K) K v (v.asIdeal ^ c) m := by
    intro m hm hcm
    refine ⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hm i j), ?_, ?_⟩
    · rw [idealBound_pow]
      have := hcm 1 0
      simpa using this
    · rw [idealBound_pow]
      have := hcm 1 1
      simpa using this
  rw [AdelicDock.mem_localLevelOne_iff]
  exact ⟨key _ hint hc, key _ hint' hc'⟩

theorem isCongMat_conj {c : ℕ} {s : GL (Fin 2) (v.adicCompletion K)}
    (hs : s ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤) {g : GL (Fin 2) (v.adicCompletion K)}
    (hg : IsCongMat K v c (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) : IsCongMat K v c ((s⁻¹ * g * s : GL (Fin 2) (v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
  rw [mem_localLevelOne_top_iff] at hs
  have hmat : ((s⁻¹ * g * s : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1
      = ((s⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) * ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1)
        * (s : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← Matrix.GeneralLinearGroup.coe_mul,
      ← Matrix.GeneralLinearGroup.coe_mul, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one]
  intro i j
  rw [hmat]
  have h1 : ∀ i j, Valued.v ((((s⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
      * ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1)) i j) ≤ 1 * WithZero.exp (-(c : ℤ)) :=
    entries_mul_le K v hs.2 hg
  have := entries_mul_le K v h1 hs.1 i j
  simpa using this

theorem conj_mem_localLevelOne_pow {c : ℕ} {s g : GL (Fin 2) (v.adicCompletion K)}
    (hs : s ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤) (hg : g ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤)
    (hgc : IsCongMat K v c (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) :
    s⁻¹ * g * s ∈ AdelicDock.localLevelOne (𝓞 K) K v (v.asIdeal ^ c) :=
  mem_localLevelOne_pow_of_isCongMat (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hs) hg) hs)
    (isCongMat_conj hs hgc)

theorem unipotent_mem_top {x : v.adicCompletion K} (hx : Valued.v x ≤ 1) :
    (UnramifiedWhittaker.unipotent x : GL (Fin 2) (v.adicCompletion K)) ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤ := by
  rw [mem_localLevelOne_top_iff, unipotent_inv]
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;> simp [unipotent_coe, hx]

theorem isCongMat_unipotent {c : ℕ} {x : v.adicCompletion K} (hx : Valued.v x ≤ WithZero.exp (-(c : ℤ))) :
    IsCongMat K v c ((UnramifiedWhittaker.unipotent x : GL (Fin 2) (v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
  have hx' : Valued.v x ≤ (WithZero.exp (c : ℤ))⁻¹ := by rwa [← WithZero.exp_neg]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [unipotent_coe, hx']

theorem lowerUni_mem_top {x : v.adicCompletion K} (hx : Valued.v x ≤ 1) :
    (lowerUni x : GL (Fin 2) (v.adicCompletion K)) ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤ := by
  rw [mem_localLevelOne_top_iff, lowerUni_inv]
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;> simp [lowerUni_coe, hx]

theorem isCongMat_lowerUni {c : ℕ} {x : v.adicCompletion K} (hx : Valued.v x ≤ WithZero.exp (-(c : ℤ))) :
    IsCongMat K v c ((lowerUni x : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
  have hx' : Valued.v x ≤ (WithZero.exp (c : ℤ))⁻¹ := by rwa [← WithZero.exp_neg]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [lowerUni_coe, hx']

theorem diagOne_mem_top {u : (v.adicCompletion K)ˣ} (hu : Valued.v (u : v.adicCompletion K) = 1) :
    (AdelicLevel.diagOne u : GL (Fin 2) (v.adicCompletion K)) ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤ := by
  have key : ∀ w : (v.adicCompletion K)ˣ, Valued.v (w : v.adicCompletion K) = 1 →
      AdelicDock.IsLocalLevelOne (𝓞 K) K v ⊤
        ((AdelicLevel.diagOne w : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
    intro w hw
    rw [isLocalLevelOne_top_iff]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [diagOne_coe, hw]
  rw [AdelicDock.mem_localLevelOne_iff, ← map_inv]
  refine ⟨key u hu, key u⁻¹ ?_⟩
  rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]

theorem isCongMat_diagOne {c : ℕ} {u : (v.adicCompletion K)ˣ} (hu : u ∈ higherUnitsAt K v c) :
    IsCongMat K v c ((AdelicLevel.diagOne u : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
  have h : Valued.v ((u : v.adicCompletion K) - 1) ≤ (WithZero.exp (c : ℤ))⁻¹ := by
    rw [← WithZero.exp_neg]; exact valued_sub_one_le_of_mem_higherUnitsAt K v hu
  intro i j
  fin_cases i <;> fin_cases j <;> simp [diagOne_coe, h]

theorem weylJ_mem_top : (weylJ : GL (Fin 2) (v.adicCompletion K)) ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤ := by
  have hinv : (weylJ : GL (Fin 2) (v.adicCompletion K))⁻¹ = gl2 0 (-1) 1 0 (by simp) := by
    rw [inv_eq_iff_mul_eq_one]
    apply gl_eq_of_entries <;> simp [mul_coe_apply, weylJ_coe]
  rw [mem_localLevelOne_top_iff, hinv]
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;> simp [weylJ_coe]

theorem scalar_mem_localLevelOne_of_mem_higherUnitsAt {c : ℕ} {u : (v.adicCompletion K)ˣ}
    (hu : u ∈ higherUnitsAt K v c) :
    (Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) (v.adicCompletion K))
      ∈ AdelicDock.localLevelOne (𝓞 K) K v (v.asIdeal ^ c) := by
  have hval : Valued.v (u : v.adicCompletion K) = 1 := hu.1
  have hval' : Valued.v ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hval, inv_one]
  have key : ∀ w : (v.adicCompletion K)ˣ, Valued.v (w : v.adicCompletion K) = 1 →
      AdelicDock.IsLocalLevelOne (𝓞 K) K v ⊤
        ((Matrix.GeneralLinearGroup.scalar (Fin 2) w : GL (Fin 2) (v.adicCompletion K)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
    intro w hw
    rw [isLocalLevelOne_top_iff]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [scalar_coe, hw]
  have hmem : (Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) (v.adicCompletion K))
      ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤ := by
    rw [AdelicDock.mem_localLevelOne_iff, ← map_inv]
    exact ⟨key u hval, key u⁻¹ hval'⟩
  refine mem_localLevelOne_pow_of_isCongMat hmem ?_
  have h : Valued.v ((u : v.adicCompletion K) - 1) ≤ (WithZero.exp (c : ℤ))⁻¹ := by
    rw [← WithZero.exp_neg]; exact valued_sub_one_le_of_mem_higherUnitsAt K v hu
  intro i j
  fin_cases i <;> fin_cases j <;> simp [scalar_coe, h]

theorem central_eq_one_of_mem_higherUnitsAt
    (W : GL (Fin 2) (v.adicCompletion K) → ℂ) (c : ℕ)
    (hK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 K) K v (v.asIdeal ^ c), ∀ g : GL (Fin 2) (v.adicCompletion K),
      W (g * k) = W g)
    (hne : W ≠ 0)
    (ω : (v.adicCompletion K)ˣ →* ℂˣ)
    (hcentral : ∀ (z : (v.adicCompletion K)ˣ) (g : GL (Fin 2) (v.adicCompletion K)),
      W (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω z : ℂˣ) : ℂ) * W g) :
    ∀ u ∈ higherUnitsAt K v c, ω u = 1 := by
  intro u hu
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, W g₀ ≠ 0 := Function.ne_iff.mp hne
  have h1 := hK _ (scalar_mem_localLevelOne_of_mem_higherUnitsAt hu) g₀
  rw [← scalar_mul_comm, hcentral] at h1
  have h2 : ((ω u : ℂˣ) : ℂ) = 1 := by
    have := mul_left_injective₀ hg₀ (h1.trans (one_mul _).symm)
    simpa using this
  exact Units.val_eq_one.mp h2

theorem hasConductorExponentAt_mul_of_forall_mem_higherUnitsAt
    (χ η : (v.adicCompletion K)ˣ →* ℂˣ) (a b : ℕ) (hχ : HasConductorExponentAt K v χ a)
    (hη : ∀ u ∈ higherUnitsAt K v b, η u = 1) (hba : b + 1 ≤ a) :
    HasConductorExponentAt K v (χ * η) a := by
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · rw [MonoidHom.mul_apply, hχ.1 u hu, hη u (higherUnitsAt_antitone K v (by omega) hu), one_mul]
  · obtain ⟨u, hu, hne⟩ := hχ.2 (max m b) (by omega)
    refine ⟨u, higherUnitsAt_antitone K v (le_max_left m b) hu, ?_⟩
    rw [MonoidHom.mul_apply, hη u (higherUnitsAt_antitone K v (le_max_right m b) hu), mul_one]
    exact hne

theorem hasConductorExponentAt_mul_of_forall_mem_higherUnitsAt'
    (η χ : (v.adicCompletion K)ˣ →* ℂˣ) (a b : ℕ) (hχ : HasConductorExponentAt K v χ a)
    (hη : ∀ u ∈ higherUnitsAt K v b, η u = 1) (hba : b + 1 ≤ a) :
    HasConductorExponentAt K v (η * χ) a := by
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · rw [MonoidHom.mul_apply, hχ.1 u hu, hη u (higherUnitsAt_antitone K v (by omega) hu), one_mul]
  · obtain ⟨u, hu, hne⟩ := hχ.2 (max m b) (by omega)
    refine ⟨u, higherUnitsAt_antitone K v (le_max_left m b) hu, ?_⟩
    rw [MonoidHom.mul_apply, hη u (higherUnitsAt_antitone K v (le_max_right m b) hu), one_mul]
    exact hne

theorem hasConductorExponentAt_inv {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ}
    (hχ : HasConductorExponentAt K v χ a) : HasConductorExponentAt K v χ⁻¹ a := by
  refine ⟨fun u hu => by rw [MonoidHom.inv_apply, hχ.1 u hu, inv_one], fun m hm => ?_⟩
  obtain ⟨u, hu, hne⟩ := hχ.2 m hm
  exact ⟨u, hu, fun h => hne (inv_eq_one.mp (by rwa [MonoidHom.inv_apply] at h))⟩

end Level

section Profiles

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}
  (W : GL (Fin 2) (v.adicCompletion K) → ℂ) (c : ℕ)
  (hK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 K) K v (v.asIdeal ^ c), ∀ g : GL (Fin 2) (v.adicCompletion K),
    W (g * k) = W g)

include hK

theorem profile_mul_higherUnit {k : GL (Fin 2) (v.adicCompletion K)}
    (hk : k ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤) (y : (v.adicCompletion K)ˣ) {u : (v.adicCompletion K)ˣ}
    (hu : u ∈ higherUnitsAt K v c) :
    W (AdelicLevel.diagOne (y * u) * k) = W (AdelicLevel.diagOne y * k) := by
  have hmem := conj_mem_localLevelOne_pow (c := c) hk (diagOne_mem_top hu.1) (isCongMat_diagOne hu)
  have := hK _ hmem (AdelicLevel.diagOne y * k)
  rw [← this, map_mul]
  congr 1
  group

theorem profile_lowerUni {k : GL (Fin 2) (v.adicCompletion K)}
    (hk : k ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤) {s : v.adicCompletion K}
    (hs : Valued.v s ≤ WithZero.exp (-(c : ℤ))) (g : GL (Fin 2) (v.adicCompletion K)) :
    W (g * lowerUni s * k) = W (g * k) := by
  have hs1 : Valued.v s ≤ 1 := hs.trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  have hmem := conj_mem_localLevelOne_pow (c := c) hk (lowerUni_mem_top hs1) (isCongMat_lowerUni hs)
  have := hK _ hmem (g * k)
  rw [← this]
  congr 1
  group

theorem profile_unipotent {k : GL (Fin 2) (v.adicCompletion K)}
    (hk : k ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤) {x : v.adicCompletion K}
    (hx : Valued.v x ≤ WithZero.exp (-(c : ℤ))) (g : GL (Fin 2) (v.adicCompletion K)) :
    W (g * UnramifiedWhittaker.unipotent x * k) = W (g * k) := by
  have hx1 : Valued.v x ≤ 1 := hx.trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  have hmem := conj_mem_localLevelOne_pow (c := c) hk (unipotent_mem_top hx1) (isCongMat_unipotent hx)
  have := hK _ hmem (g * k)
  rw [← this]
  congr 1
  group

variable (ψ : AddChar (v.adicCompletion K) ℂ)
  (hlaw : ∀ (x : v.adicCompletion K) (g : GL (Fin 2) (v.adicCompletion K)),
    W (UnramifiedWhittaker.unipotent x * g) = ψ x * W g)
  (hψ' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ ψ x ≠ 1)

include hlaw hψ'

theorem profile_eq_zero_of_le_valued {k : GL (Fin 2) (v.adicCompletion K)}
    (hk : k ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤) (y : (v.adicCompletion K)ˣ)
    (hy : WithZero.exp ((c : ℤ) + 1) ≤ Valued.v (y : v.adicCompletion K)) :
    W (AdelicLevel.diagOne y * k) = 0 := by
  obtain ⟨x, hx1, hψx⟩ := hψ'

  set t : v.adicCompletion K := ((y⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) * x with ht_def
  have hyt : (y : v.adicCompletion K) * t = x := by rw [ht_def, ← mul_assoc, Units.mul_inv, one_mul]
  have hy0 : Valued.v (y : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  have ht : Valued.v t ≤ WithZero.exp (-(c : ℤ)) := by
    rw [ht_def, Valuation.map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (y : v.adicCompletion K) = WithZero.exp m :=
      ⟨_, (WithZero.exp_log hy0).symm⟩
    rw [hm] at hy ⊢
    rw [WithZero.exp_le_exp] at hy
    rw [← WithZero.exp_neg]
    calc WithZero.exp (-m) * Valued.v x ≤ WithZero.exp (-m) * WithZero.exp 1 := mul_le_mul_right hx1 _
      _ = WithZero.exp (-m + 1) := (WithZero.exp_add _ _).symm
      _ ≤ WithZero.exp (-(c : ℤ)) := WithZero.exp_le_exp.mpr (by omega)
  have h1 := profile_unipotent W c hK hk ht (AdelicLevel.diagOne y)
  rw [diagOne_mul_unipotent, mul_assoc, hlaw, hyt] at h1
  have h2 : (ψ x - 1) * W (AdelicLevel.diagOne y * k) = 0 := by
    rw [sub_mul, one_mul, h1, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) hψx
  · exact h3

end Profiles

section Units

theorem borelSpace_units {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
    [MeasurableSpace G₀] [BorelSpace G₀] : BorelSpace G₀ˣ := by
  refine ⟨?_⟩
  have hind : (inferInstance : TopologicalSpace G₀ˣ) = TopologicalSpace.induced Units.val inferInstance :=
    (Units.isEmbedding_val₀ (G₀ := G₀)).eq_induced
  show MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace G₀) = borel G₀ˣ
  rw [BorelSpace.measurable_eq (α := G₀), ← borel_comap, ← hind]

end Units

section Padic

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

variable (p : HeightOneSpectrum (𝓞 ℚ))

scoped instance borelSpace_units_padic : BorelSpace (p.adicCompletion ℚ)ˣ := borelSpace_units

scoped instance measurableMul_units_padic : MeasurableMul (p.adicCompletion ℚ)ˣ := by infer_instance

abbrev USet : Set (p.adicCompletion ℚ)ˣ := {u | Valued.v (u : p.adicCompletion ℚ) = 1}

abbrev UF : Set (p.adicCompletion ℚ) := {x | Valued.v x = 1}

def mulHaar : Measure (p.adicCompletion ℚ)ˣ := Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))

theorem valued_uniformizerUnit_zpow (m : ℤ) :
    Valued.v ((uniformizerUnit ℚ p ^ m : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = WithZero.exp (-m) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem norm_eq_zpow_of_valued {x : p.adicCompletion ℚ} {m : ℤ} (hx : Valued.v x = WithZero.exp m) :
    ‖x‖ = (Ideal.absNorm p.asIdeal : ℝ) ^ m := by
  rw [NumberField.FinitePlace.norm_def, hx,
    show (WithZero.exp m) = ((Multiplicative.ofAdd m : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      from rfl,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe, toAdd_ofAdd,
    NNReal.coe_zpow, NNReal.coe_natCast]

theorem modulus_eq_one_of_valued {u : p.adicCompletion ℚ} (hu : Valued.v u = 1) : modulus u = 1 := by
  rw [← NNReal.coe_inj, NNReal.coe_one, modulus_adicCompletion_eq_nnnorm ℚ p u, coe_nnnorm,
    norm_eq_zpow_of_valued p (m := 0) (by rw [hu, WithZero.exp_zero]), zpow_zero]

theorem measurable_modulus : Measurable (fun x : p.adicCompletion ℚ => modulus x) := by
  have : (fun x : p.adicCompletion ℚ => modulus x) = fun x => ‖x‖₊ := by
    funext x; exact modulus_adicCompletion_eq_nnnorm ℚ p x
  rw [this]
  exact measurable_nnnorm

theorem isClosed_ball (k : ℤ) : IsClosed {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp k} := by
  have ht : ((uniformizerUnit ℚ p ^ (-k) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) ≠ 0 :=
    Units.ne_zero _
  have h := isClosed_setOf_valued_le p _ ht
  rw [valued_uniformizerUnit_zpow, neg_neg] at h
  exact h

theorem isOpen_ball (k : ℤ) : IsOpen {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp k} := by
  have ht : ((uniformizerUnit ℚ p ^ (-k) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) ≠ 0 :=
    Units.ne_zero _
  have h := isOpen_setOf_valued_le p _ ht
  rw [valued_uniformizerUnit_zpow, neg_neg] at h
  exact h

theorem UF_eq_diff :
    UF p = {y : p.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (0 : ℤ)}
          \ {y : p.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (-(1 : ℤ))} := by
  ext y
  simp only [UF, Set.mem_setOf_eq, Set.mem_diff]
  constructor
  · intro hy
    refine ⟨by rw [hy, WithZero.exp_zero], fun h => ?_⟩
    rw [hy, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
    omega
  · rintro ⟨h1, h2⟩
    have hne : Valued.v y ≠ 0 := fun h0 => h2 (by rw [h0]; exact zero_le')
    obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v y = WithZero.exp m := ⟨_, (WithZero.exp_log hne).symm⟩
    rw [hm, WithZero.exp_le_exp] at h1 h2
    rw [hm, ← WithZero.exp_zero]
    congr 1
    omega

theorem isClosed_UF : IsClosed (UF p) := by
  rw [UF_eq_diff]
  exact (isClosed_ball p _).sdiff (isOpen_ball p _)

theorem measurableSet_UF : MeasurableSet (UF p) := (isClosed_UF p).measurableSet

theorem coe_integers_eq :
    ((p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ))) = {x | Valued.v x ≤ WithZero.exp 0} := by
  ext x
  rw [WithZero.exp_zero]
  exact HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p

theorem isCompact_ball_zero : IsCompact {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp 0} := by
  rw [← coe_integers_eq]
  exact isCompact_iff_compactSpace.mpr (show CompactSpace (p.adicCompletionIntegers ℚ) from inferInstance)

theorem isCompact_UF : IsCompact (UF p) := by
  refine (isCompact_ball_zero p).of_isClosed_subset (isClosed_UF p) fun u hu => ?_
  have hu' : Valued.v u = 1 := hu
  show Valued.v u ≤ WithZero.exp 0
  rw [hu', WithZero.exp_zero]

theorem measurableSet_USet : MeasurableSet (USet p) :=
  ((isClosed_UF p).preimage Units.continuous_val).measurableSet

theorem ne_zero_of_mem_UF {x : p.adicCompletion ℚ} (hx : x ∈ UF p) : x ≠ 0 :=
  (Valuation.ne_zero_iff _).mp (by rw [show Valued.v x = 1 from hx]; exact one_ne_zero)

scoped instance isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  set c : ℝ≥0 := (Ideal.absNorm p.asIdeal : ℝ≥0) ^ (-(addCharLevel (psiLocal ℚ p) : ℝ) / 2) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot))).ne'
  have hdef : selfDualHaarAt ℚ p = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

scoped instance isHaarMeasure_mulHaar : (mulHaar p).IsHaarMeasure :=
  isHaarMeasure_comap_val_mulMeasure ℚ p (selfDualHaarAt ℚ p)

theorem measurableEmbedding_val :
    MeasurableEmbedding (Units.val : (p.adicCompletion ℚ)ˣ → p.adicCompletion ℚ) := by
  refine (Topology.IsOpenEmbedding.measurableEmbedding ⟨Units.isEmbedding_val₀, ?_⟩)
  have : Set.range (Units.val : (p.adicCompletion ℚ)ˣ → p.adicCompletion ℚ) = {0}ᶜ := by
    ext x
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩
  rw [this]
  exact isClosed_singleton.isOpen_compl

theorem setIntegral_USet_eq (G : p.adicCompletion ℚ → ℂ) :
    ∫ u in USet p, G (u : p.adicCompletion ℚ) ∂(mulHaar p) = ∫ x in UF p, G x ∂(selfDualHaarAt ℚ p) := by
  have hemb := measurableEmbedding_val p

  have h1 : ∫ u in USet p, G (u : p.adicCompletion ℚ) ∂(mulHaar p)
      = ∫ x in UF p, G x ∂(Measure.map Units.val (mulHaar p)) := by
    rw [hemb.setIntegral_map]
    rfl
  rw [h1, mulHaar, hemb.map_comap, Measure.restrict_restrict (measurableSet_UF p)]
  have hsub : UF p ∩ Set.range (Units.val : (p.adicCompletion ℚ)ˣ → p.adicCompletion ℚ) = UF p := by
    refine Set.inter_eq_left.mpr fun x hx => ⟨Units.mk0 x (ne_zero_of_mem_UF p hx), rfl⟩
  rw [hsub]

  rw [mulMeasure, restrict_withDensity (measurableSet_UF p), Measure.restrict_restrict (measurableSet_UF p)]
  have hsub' : UF p ∩ ({0}ᶜ : Set (p.adicCompletion ℚ)) = UF p :=
    Set.inter_eq_left.mpr fun x hx => ne_zero_of_mem_UF p hx
  rw [hsub']
  have hmeas : Measurable fun x : p.adicCompletion ℚ => ((modulus x : ℝ≥0) : ℝ≥0∞)⁻¹ :=
    (measurable_modulus p).coe_nnreal_ennreal.inv
  have hlt : ∀ᵐ x ∂((selfDualHaarAt ℚ p).restrict (UF p)), ((modulus x : ℝ≥0) : ℝ≥0∞)⁻¹ < ⊤ := by
    rw [ae_restrict_iff' (measurableSet_UF p)]
    refine Filter.Eventually.of_forall fun x hx => ?_
    rw [ENNReal.inv_lt_top, ENNReal.coe_pos]
    exact modulus_pos (ne_zero_of_mem_UF p hx)
  rw [integral_withDensity_eq_integral_toReal_smul hmeas hlt]
  refine setIntegral_congr_fun (measurableSet_UF p) fun x hx => ?_
  show (((modulus x : ℝ≥0) : ℝ≥0∞)⁻¹).toReal • G x = G x
  rw [modulus_eq_one_of_valued p hx]
  simp

theorem psi_level_data :
    (∀ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (0 : ℤ) → psiLocal ℚ p x = 1) ∧
      ∃ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧ psiLocal ℚ p x ≠ 1 := by
  have h := LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ p (psiLocal ℚ p)
    ⟨0, fun x hx => LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ p x
      ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).mpr (by simpa using hx))⟩
    (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p)
  rwa [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat] at h

theorem continuous_psiLocal : Continuous (psiLocal ℚ p) := by
  obtain ⟨hψn, -⟩ := psi_level_data p
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hmem : (fun y => y - x) ⁻¹' {h : p.adicCompletion ℚ | Valued.v h ≤ WithZero.exp 0} ∈ nhds x := by
    refine ((isOpen_ball p 0).preimage (continuous_id.sub continuous_const)).mem_nhds ?_
    show Valued.v (x - x) ≤ WithZero.exp 0
    rw [sub_self, map_zero]
    exact zero_le'
  have hev : (fun _ => psiLocal ℚ p x) =ᶠ[nhds x] (psiLocal ℚ p : p.adicCompletion ℚ → ℂ) := by
    refine Filter.mem_of_superset hmem fun y hy => ?_
    show psiLocal ℚ p x = psiLocal ℚ p y
    rw [show psiLocal ℚ p y = psiLocal ℚ p (x + (y - x)) by rw [add_sub_cancel], AddChar.map_add_eq_mul,
      hψn _ hy, mul_one]
  exact continuousAt_const.congr hev

theorem charExt_eq_of_valued_sub_le {χ : (p.adicCompletion ℚ)ˣ →* ℂˣ} {a : ℕ}
    (hχ : ∀ u ∈ higherUnitsAt ℚ p a, χ u = 1) {y₀ y : p.adicCompletion ℚ} (hy₀ : y₀ ≠ 0)
    (h : Valued.v (y - y₀) ≤ Valued.v y₀ * WithZero.exp (-((a + 1 : ℕ) : ℤ))) :
    charExt χ y = charExt χ y₀ := by
  have hv0 : Valued.v y₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hy₀
  obtain ⟨m₀, hm₀⟩ : ∃ m : ℤ, Valued.v y₀ = WithZero.exp m := ⟨_, (WithZero.exp_log hv0).symm⟩
  have h' : Valued.v (y - y₀) ≤ WithZero.exp (m₀ + -((a + 1 : ℕ) : ℤ)) := by
    rwa [hm₀, ← WithZero.exp_add] at h
  have hlt : Valued.v (y - y₀) < Valued.v y₀ := by
    refine h'.trans_lt ?_
    rw [hm₀, WithZero.exp_lt_exp]
    omega
  have hyy : Valued.v y = Valued.v y₀ := Valuation.map_eq_of_sub_lt _ hlt
  have hy : y ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hyy]; exact hv0)
  set u : (p.adicCompletion ℚ)ˣ := Units.mk0 y hy * (Units.mk0 y₀ hy₀)⁻¹ with hu
  have huval : (u : p.adicCompletion ℚ) = y * y₀⁻¹ := by simp [hu]
  have humem : u ∈ higherUnitsAt ℚ p a := by
    refine ⟨?_, Or.inr ?_⟩
    · rw [huval, map_mul, map_inv₀, hyy, mul_inv_cancel₀ hv0]
    · have hsub : (u : p.adicCompletion ℚ) - 1 = y₀⁻¹ * (y - y₀) := by
        rw [huval, mul_sub, inv_mul_cancel₀ hy₀, mul_comm y₀⁻¹ y]
      rw [hsub, map_mul, map_inv₀, hm₀, ← WithZero.exp_neg]
      calc WithZero.exp (-m₀) * Valued.v (y - y₀)
          ≤ WithZero.exp (-m₀) * WithZero.exp (m₀ + -((a + 1 : ℕ) : ℤ)) := mul_le_mul_right h' _
        _ = WithZero.exp (-((a + 1 : ℕ) : ℤ)) := by rw [← WithZero.exp_add]; congr 1; omega
        _ ≤ WithZero.exp (-(a : ℤ)) := WithZero.exp_le_exp.mpr (by push_cast; omega)
  have hmk : Units.mk0 y hy = u * Units.mk0 y₀ hy₀ := by rw [hu, inv_mul_cancel_right]
  rw [charExt_of_ne_zero χ hy, charExt_of_ne_zero χ hy₀, hmk, map_mul, hχ u humem, one_mul]

theorem continuousOn_charExt_UF {χ : (p.adicCompletion ℚ)ˣ →* ℂˣ} {a : ℕ}
    (hχ : ∀ u ∈ higherUnitsAt ℚ p a, χ u = 1) : ContinuousOn (charExt χ) (UF p) := by
  intro y₀ hy₀
  have hy₀' : y₀ ≠ 0 := ne_zero_of_mem_UF p hy₀
  set t : p.adicCompletion ℚ :=
    y₀ * ((uniformizerUnit ℚ p ^ ((a + 1 : ℕ) : ℤ) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) with ht
  have ht0 : t ≠ 0 := mul_ne_zero hy₀' (Units.ne_zero _)
  have hvt : Valued.v t = Valued.v y₀ * WithZero.exp (-((a + 1 : ℕ) : ℤ)) := by
    rw [ht, map_mul, valued_uniformizerUnit_zpow]
  have hmem : (fun y => y - y₀) ⁻¹' {h : p.adicCompletion ℚ | Valued.v h ≤ Valued.v t} ∈ nhds y₀ := by
    refine ((isOpen_setOf_valued_le p t ht0).preimage (continuous_id.sub continuous_const)).mem_nhds ?_
    show Valued.v (y₀ - y₀) ≤ Valued.v t
    rw [sub_self, map_zero]
    exact zero_le'
  have hev : charExt χ =ᶠ[nhdsWithin y₀ (UF p)] fun _ => charExt χ y₀ :=
    Filter.mem_of_superset (mem_nhdsWithin_of_mem_nhds hmem) fun y hy =>
      charExt_eq_of_valued_sub_le p hχ hy₀' (by rw [← hvt]; exact hy)
  exact (continuousWithinAt_const.congr_of_eventuallyEq hev
    (by simp : charExt χ y₀ = (fun _ => charExt χ y₀) y₀))

theorem integrableOn_psi_mul_charExt {η : (p.adicCompletion ℚ)ˣ →* ℂˣ} {b : ℕ}
    (hη : ∀ u ∈ higherUnitsAt ℚ p b, η u = 1) (z : p.adicCompletion ℚ) :
    IntegrableOn (fun x => psiLocal ℚ p (z * x) * charExt η x) (UF p) (selfDualHaarAt ℚ p) := by
  refine ContinuousOn.integrableOn_compact (isCompact_UF p) ?_
  exact ((continuous_psiLocal p).comp (continuous_const.mul continuous_id)).continuousOn.mul
    (continuousOn_charExt_UF p hη)

theorem twisted_moment_eq_zero_of_valued_ne
    (f : p.adicCompletion ℚ → ℂ) (c : ℕ)
    (hf : ∀ u : (p.adicCompletion ℚ)ˣ, Valued.v (u : p.adicCompletion ℚ) = 1 →
      ∀ w ∈ higherUnitsAt ℚ p c, f ((u : p.adicCompletion ℚ) * w) = f u)
    (ν : (p.adicCompletion ℚ)ˣ →* ℂˣ) (a : ℕ) (ha : 1 ≤ a) (hca : c + 1 ≤ a) (hν : HasConductorExponentAt ℚ p ν a)
    (z : p.adicCompletion ℚ) (hz : Valued.v z ≠ WithZero.exp (a : ℤ)) :
    ∫ x in UF p, psiLocal ℚ p (z * x) * f x * charExt ν x ∂(selfDualHaarAt ℚ p) = 0 := by
  obtain ⟨hψn, hψn'⟩ := psi_level_data p

  obtain ⟨S, coef, hS, -, hexp⟩ :=
    LanglandsTunnell.TateLocal.exists_finset_hasConductorExponentAt_le_eq_sum_of_forall_mem_higherUnitsAt ℚ p c
      (fun u : (p.adicCompletion ℚ)ˣ => f u) hf

  have hηc : ∀ η ∈ S, ∀ u ∈ higherUnitsAt ℚ p c, η u = 1 := by
    intro η hη u hu
    obtain ⟨m, hm, hηm⟩ := hS η hη
    exact hηm.1 u (higherUnitsAt_antitone ℚ p hm hu)
  have hcond : ∀ η ∈ S, HasConductorExponentAt ℚ p (η * ν) a := fun η hη =>
    hasConductorExponentAt_mul_of_forall_mem_higherUnitsAt' η ν a c hν (hηc η hη) hca

  have hcongr : ∀ x ∈ UF p, psiLocal ℚ p (z * x) * f x * charExt ν x
      = ∑ η ∈ S, coef η * (psiLocal ℚ p (z * x) * charExt (η * ν) x) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_zero_of_mem_UF p hx
    have hx1 : Valued.v x = 1 := hx
    have hfx : f x = ∑ η ∈ S, coef η * ((η (Units.mk0 x hx0) : ℂˣ) : ℂ) := by
      have := hexp (Units.mk0 x hx0) (by rw [Units.val_mk0]; exact hx1)
      rwa [Units.val_mk0] at this
    rw [hfx, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun η _ => ?_
    rw [charExt_of_ne_zero _ hx0, charExt_of_ne_zero _ hx0, MonoidHom.mul_apply, Units.val_mul]
    ring
  rw [setIntegral_congr_fun (measurableSet_UF p) hcongr, integral_finset_sum]
  · refine Finset.sum_eq_zero fun η hη => ?_
    rw [integral_const_mul]
    have hηνa : ∀ u ∈ higherUnitsAt ℚ p a, (η * ν) u = 1 := (hcond η hη).1
    have hz' : Valued.v z ≠ WithZero.exp ((0 : ℤ) + a) := by rwa [zero_add]
    rw [LanglandsTunnell.TateLocal.setIntegral_addChar_mul_charExt_eq_zero_of_valued_ne ℚ p (selfDualHaarAt ℚ p)
      (psiLocal ℚ p) 0 hψn hψn' (η * ν) a ha (hcond η hη) z hz', mul_zero]
  · intro η hη
    exact ((integrableOn_psi_mul_charExt p (hcond η hη).1 z).const_mul (coef η))

def hDepth (a : ℕ) : ℕ := (a - 1) / 2 + 1

theorem one_le_hDepth (a : ℕ) : 1 ≤ hDepth a := by unfold hDepth; omega

theorem le_two_mul_hDepth (a : ℕ) : a ≤ 2 * hDepth a := by unfold hDepth; omega

theorem le_sub_hDepth {a c : ℕ} (h : 2 * c + 1 ≤ a) : c ≤ a - hDepth a := by unfold hDepth; omega

theorem twisted_moment_eq_apply_mul
    (f : p.adicCompletion ℚ → ℂ) (c : ℕ)
    (hf : ∀ u : (p.adicCompletion ℚ)ˣ, Valued.v (u : p.adicCompletion ℚ) = 1 →
      ∀ w ∈ higherUnitsAt ℚ p c, f ((u : p.adicCompletion ℚ) * w) = f u)
    (ν : (p.adicCompletion ℚ)ˣ →* ℂˣ) (a : ℕ) (hca : 2 * c + 1 ≤ a) (hν : HasConductorExponentAt ℚ p ν a)
    (cν : p.adicCompletion ℚ)
    (hcν : ∀ u ∈ higherUnitsAt ℚ p (hDepth a), ((ν u : ℂˣ) : ℂ) = psiLocal ℚ p (cν * ((u : p.adicCompletion ℚ) - 1)))
    (z : p.adicCompletion ℚ) (hz : Valued.v z = WithZero.exp (a : ℤ))
    (u₁ : p.adicCompletion ℚ) (hu₁ : Valued.v u₁ = 1)
    (hgood : Valued.v (z * u₁ + cν) ≤ WithZero.exp ((hDepth a : ℕ) : ℤ)) :
    ∫ x in UF p, psiLocal ℚ p (z * x) * f x * charExt ν x ∂(selfDualHaarAt ℚ p)
      = f u₁ * ∫ x in UF p, psiLocal ℚ p (z * x) * charExt ν x ∂(selfDualHaarAt ℚ p) := by
  obtain ⟨hψn, hψn'⟩ := psi_level_data p
  have hf' : ∀ u : (p.adicCompletion ℚ)ˣ, Valued.v (u : p.adicCompletion ℚ) = 1 →
      ∀ w ∈ higherUnitsAt ℚ p (a - hDepth a), f ((u : p.adicCompletion ℚ) * w) = f u :=
    fun u hu w hw => hf u hu w (higherUnitsAt_antitone ℚ p (le_sub_hDepth hca) hw)
  have hz' : Valued.v z = WithZero.exp ((0 : ℤ) + a) := by rwa [zero_add]
  have key := (LanglandsTunnell.TateLocal.setIntegral_addChar_mul_mul_charExt_eq_apply_mul_setIntegral_of_forall_mem_higherUnitsAt
    ℚ p (selfDualHaarAt ℚ p) (psiLocal ℚ p) 0 hψn hψn' ν a (hDepth a) (one_le_hDepth a) (le_two_mul_hDepth a)
    hν.1 cν hcν z hz' f hf').1 u₁ hu₁ (by rwa [zero_add])
  exact key

theorem inv_inv_char (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) : χ⁻¹⁻¹ = χ := by
  ext u
  rw [MonoidHom.inv_apply, MonoidHom.inv_apply, inv_inv]

def halfPow (a : ℕ) : ℂ := (Ideal.absNorm p.asIdeal : ℂ) ^ (((addCharLevel (psiLocal ℚ p) + a : ℤ) : ℂ) / 2)

theorem halfPow_ne_zero (a : ℕ) : halfPow p a ≠ 0 := by
  unfold halfPow
  have h0 : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot)
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl h0)

theorem gauss_eval {η : (p.adicCompletion ℚ)ˣ →* ℂˣ} {a : ℕ} (ha : 1 ≤ a) (hη : HasConductorExponentAt ℚ p η a)
    (hηu : ‖(η (uniformizerUnit ℚ p) : ℂ)‖ = 1) {z : p.adicCompletion ℚ} (hz : Valued.v z = WithZero.exp (a : ℤ)) :
    (∫ x in UF p, psiLocal ℚ p (z * x) * charExt η⁻¹ x ∂(selfDualHaarAt ℚ p)) * halfPow p a
      = charExt η z * stdRootNumberAt ℚ p η := by
  have hz' : Valued.v z = WithZero.exp (addCharLevel (psiLocal ℚ p) + a) := by
    rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat, zero_add]; exact hz
  exact LanglandsTunnell.TateLocal.setIntegral_psiLocal_mul_charExt_inv_mul_cpow_eq_charExt_mul_stdRootNumberAt
    ℚ p η a ha hη hηu z hz'

theorem gauss_ne_zero {ν : (p.adicCompletion ℚ)ˣ →* ℂˣ} {a : ℕ} (ha : 1 ≤ a) (hν : HasConductorExponentAt ℚ p ν a)
    (hνu : ‖(ν (uniformizerUnit ℚ p) : ℂ)‖ = 1) {z : p.adicCompletion ℚ} (hz : Valued.v z = WithZero.exp (a : ℤ)) :
    (∫ x in UF p, psiLocal ℚ p (z * x) * charExt ν x ∂(selfDualHaarAt ℚ p)) ≠ 0 := by
  have hν' : HasConductorExponentAt ℚ p ν⁻¹ a := hasConductorExponentAt_inv hν
  have hνu' : ‖(ν⁻¹ (uniformizerUnit ℚ p) : ℂ)‖ = 1 := by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hνu, inv_one]
  have key := gauss_eval p ha hν' hνu' hz
  rw [inv_inv_char] at key
  intro h0
  rw [h0, zero_mul] at key
  have hz0 : z ≠ 0 := fun h => by rw [h, map_zero] at hz; exact WithZero.exp_ne_zero.symm hz |>.elim
  have h1 : charExt ν⁻¹ z ≠ 0 := by rw [charExt_of_ne_zero _ hz0]; exact Units.ne_zero _
  have h2 : stdRootNumberAt ℚ p ν⁻¹ ≠ 0 :=
    LanglandsTunnell.TateLocal.stdRootNumberAt_ne_zero_of_hasConductorExponentAt ℚ p ν⁻¹ a ha hν' hνu'
  exact mul_ne_zero h1 h2 key.symm

theorem exists_good_unit {ν : (p.adicCompletion ℚ)ˣ →* ℂˣ} {a : ℕ} (ha : 1 ≤ a) (hν : HasConductorExponentAt ℚ p ν a)
    (hνu : ‖(ν (uniformizerUnit ℚ p) : ℂ)‖ = 1)
    (cν : p.adicCompletion ℚ)
    (hcν : ∀ u ∈ higherUnitsAt ℚ p (hDepth a), ((ν u : ℂˣ) : ℂ) = psiLocal ℚ p (cν * ((u : p.adicCompletion ℚ) - 1)))
    {z : p.adicCompletion ℚ} (hz : Valued.v z = WithZero.exp (a : ℤ)) :
    ∃ u₁ : p.adicCompletion ℚ, Valued.v u₁ = 1 ∧ Valued.v (z * u₁ + cν) ≤ WithZero.exp ((hDepth a : ℕ) : ℤ) := by
  obtain ⟨hψn, hψn'⟩ := psi_level_data p
  by_contra hall
  push Not at hall
  have hz' : Valued.v z = WithZero.exp ((0 : ℤ) + a) := by rwa [zero_add]
  have h1 : ∀ u : (p.adicCompletion ℚ)ˣ, Valued.v (u : p.adicCompletion ℚ) = 1 →
      ∀ w ∈ higherUnitsAt ℚ p (a - hDepth a), (fun _ => (1 : ℂ)) ((u : p.adicCompletion ℚ) * w)
        = (fun _ => (1 : ℂ)) u := fun _ _ _ _ => rfl
  have key := (LanglandsTunnell.TateLocal.setIntegral_addChar_mul_mul_charExt_eq_apply_mul_setIntegral_of_forall_mem_higherUnitsAt
    ℚ p (selfDualHaarAt ℚ p) (psiLocal ℚ p) 0 hψn hψn' ν a (hDepth a) (one_le_hDepth a) (le_two_mul_hDepth a)
    hν.1 cν hcν z hz' (fun _ => (1 : ℂ)) h1).2 (fun u hu => by have := hall u hu; rwa [zero_add])
  simp only [mul_one] at key
  exact gauss_ne_zero p ha hν hνu hz key

end Padic

section Core

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

variable (p : HeightOneSpectrum (𝓞 ℚ))
  (W : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (c : ℕ)
  (hK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ c), ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
    W (g * k) = W g)

open Classical in

def profileExt (k : GL (Fin 2) (p.adicCompletion ℚ)) (x : p.adicCompletion ℚ) : ℂ :=
  if h : x = 0 then 0 else W (AdelicLevel.diagOne (Units.mk0 x h) * k)

theorem profileExt_coe (k : GL (Fin 2) (p.adicCompletion ℚ)) (y : (p.adicCompletion ℚ)ˣ) :
    profileExt p W k (y : p.adicCompletion ℚ) = W (AdelicLevel.diagOne y * k) := by
  simp only [profileExt, dif_neg y.ne_zero, Units.mk0_val]

include hK in
theorem profileExt_invariant {k : GL (Fin 2) (p.adicCompletion ℚ)} (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤)
    (y₀ : (p.adicCompletion ℚ)ˣ) :
    ∀ u : (p.adicCompletion ℚ)ˣ, Valued.v (u : p.adicCompletion ℚ) = 1 →
      ∀ w ∈ higherUnitsAt ℚ p c,
        (fun x => profileExt p W k ((y₀ : p.adicCompletion ℚ) * x)) ((u : p.adicCompletion ℚ) * w)
          = (fun x => profileExt p W k ((y₀ : p.adicCompletion ℚ) * x)) u := by
  intro u _ w hw
  show profileExt p W k ((y₀ : p.adicCompletion ℚ) * ((u : p.adicCompletion ℚ) * w))
    = profileExt p W k ((y₀ : p.adicCompletion ℚ) * u)
  rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, profileExt_coe, profileExt_coe, ← mul_assoc]
  exact profile_mul_higherUnit W c hK hk (y₀ * u) hw

include hK in

theorem shellIntegral_eq_zero_of_valued_ne {k : GL (Fin 2) (p.adicCompletion ℚ)}
    (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤)
    (ν : (p.adicCompletion ℚ)ˣ →* ℂˣ) (a : ℕ) (ha : 1 ≤ a) (hca : c + 1 ≤ a) (hν : HasConductorExponentAt ℚ p ν a)
    (y₀ : (p.adicCompletion ℚ)ˣ) (s : p.adicCompletion ℚ)
    (hs : Valued.v ((y₀ : p.adicCompletion ℚ) * s) ≠ WithZero.exp (a : ℤ)) :
    ∫ u in USet p, psiLocal ℚ p (((y₀ * u : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * s)
        * W (AdelicLevel.diagOne (y₀ * u) * k) * ((ν u : ℂˣ) : ℂ) ∂(mulHaar p) = 0 := by
  set G : p.adicCompletion ℚ → ℂ := fun x => psiLocal ℚ p (((y₀ : p.adicCompletion ℚ) * s) * x)
    * profileExt p W k ((y₀ : p.adicCompletion ℚ) * x) * charExt ν x with hG
  have hcongr : ∀ u ∈ USet p, psiLocal ℚ p (((y₀ * u : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * s)
      * W (AdelicLevel.diagOne (y₀ * u) * k) * ((ν u : ℂˣ) : ℂ) = G (u : p.adicCompletion ℚ) := by
    intro u _
    simp only [hG]
    rw [← Units.val_mul, profileExt_coe, charExt_coe_units, Units.val_mul]
    congr 2
    ring
  rw [setIntegral_congr_fun (measurableSet_USet p) hcongr, setIntegral_USet_eq p G, hG]
  exact twisted_moment_eq_zero_of_valued_ne p _ c (profileExt_invariant p W c hK hk y₀) ν a ha hca hν _ hs

include hK in

theorem shellIntegral_eq_apply_mul {k : GL (Fin 2) (p.adicCompletion ℚ)}
    (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤)
    (ν : (p.adicCompletion ℚ)ˣ →* ℂˣ) (a : ℕ) (hca : 2 * c + 1 ≤ a) (hν : HasConductorExponentAt ℚ p ν a)
    (cν : p.adicCompletion ℚ)
    (hcν : ∀ u ∈ higherUnitsAt ℚ p (hDepth a), ((ν u : ℂˣ) : ℂ) = psiLocal ℚ p (cν * ((u : p.adicCompletion ℚ) - 1)))
    (y₀ : (p.adicCompletion ℚ)ˣ) (s : p.adicCompletion ℚ)
    (hs : Valued.v ((y₀ : p.adicCompletion ℚ) * s) = WithZero.exp (a : ℤ))
    (u₁ : p.adicCompletion ℚ) (hu₁ : Valued.v u₁ = 1)
    (hgood : Valued.v ((y₀ : p.adicCompletion ℚ) * s * u₁ + cν) ≤ WithZero.exp ((hDepth a : ℕ) : ℤ)) :
    ∫ u in USet p, psiLocal ℚ p (((y₀ * u : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * s)
        * W (AdelicLevel.diagOne (y₀ * u) * k) * ((ν u : ℂˣ) : ℂ) ∂(mulHaar p)
      = profileExt p W k ((y₀ : p.adicCompletion ℚ) * u₁)
          * ∫ x in UF p, psiLocal ℚ p (((y₀ : p.adicCompletion ℚ) * s) * x) * charExt ν x ∂(selfDualHaarAt ℚ p) := by
  set G : p.adicCompletion ℚ → ℂ := fun x => psiLocal ℚ p (((y₀ : p.adicCompletion ℚ) * s) * x)
    * profileExt p W k ((y₀ : p.adicCompletion ℚ) * x) * charExt ν x with hG
  have hcongr : ∀ u ∈ USet p, psiLocal ℚ p (((y₀ * u : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * s)
      * W (AdelicLevel.diagOne (y₀ * u) * k) * ((ν u : ℂˣ) : ℂ) = G (u : p.adicCompletion ℚ) := by
    intro u _
    simp only [hG]
    rw [← Units.val_mul, profileExt_coe, charExt_coe_units, Units.val_mul]
    congr 2
    ring
  rw [setIntegral_congr_fun (measurableSet_USet p) hcongr, setIntegral_USet_eq p G, hG]
  exact twisted_moment_eq_apply_mul p _ c (profileExt_invariant p W c hK hk y₀) ν a hca hν cν hcν _ hs u₁ hu₁ hgood

end Core

section GaussIdentity

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem gauss_identity (χ ω : (p.adicCompletion ℚ)ˣ →* ℂˣ) (a : ℕ) (ha : 1 ≤ a)
    (hχ : HasConductorExponentAt ℚ p χ a) (hχω : HasConductorExponentAt ℚ p (χ * ω) a)
    (hχu : ‖(χ (uniformizerUnit ℚ p) : ℂ)‖ = 1) (hχωu : ‖((χ * ω) (uniformizerUnit ℚ p) : ℂ)‖ = 1)
    (tu : (p.adicCompletion ℚ)ˣ) (n₀ m₀ : ℤ) (hnm : n₀ + m₀ = -2 * (a : ℤ))
    (hz : Valued.v (((uniformizerUnit ℚ p ^ n₀ * tu : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ)
      = WithZero.exp (a : ℤ))
    (hzt : Valued.v (((-(uniformizerUnit ℚ p ^ m₀ * tu⁻¹) : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ)
      = WithZero.exp (a : ℤ)) :
    (((χ * ω) (uniformizerUnit ℚ p) : ℂˣ) : ℂ) ^ (-m₀) * ((ω (-tu) : ℂˣ) : ℂ) *
        ∫ x in UF p, psiLocal ℚ p ((((-(uniformizerUnit ℚ p ^ m₀ * tu⁻¹) : (p.adicCompletion ℚ)ˣ)) :
          p.adicCompletion ℚ) * x) * charExt (χ * ω)⁻¹ x ∂(selfDualHaarAt ℚ p)
      = stdRootNumberAt ℚ p (χ * ω) * stdRootNumberAt ℚ p χ * (((χ (uniformizerUnit ℚ p) : ℂˣ) : ℂ) ^ n₀ *
        ∫ x in UF p, psiLocal ℚ p ((((uniformizerUnit ℚ p ^ n₀ * tu : (p.adicCompletion ℚ)ˣ)) :
          p.adicCompletion ℚ) * x) * charExt χ x ∂(selfDualHaarAt ℚ p)) := by
  set ϖ := uniformizerUnit ℚ p with hϖ
  set zu : (p.adicCompletion ℚ)ˣ := ϖ ^ n₀ * tu with hzu
  set ztu : (p.adicCompletion ℚ)ˣ := -(ϖ ^ m₀ * tu⁻¹) with hztu
  set Gz := ∫ x in UF p, psiLocal ℚ p ((zu : p.adicCompletion ℚ) * x) * charExt χ x ∂(selfDualHaarAt ℚ p) with hGz
  set Gzt := ∫ x in UF p, psiLocal ℚ p ((ztu : p.adicCompletion ℚ) * x) * charExt (χ * ω)⁻¹ x
    ∂(selfDualHaarAt ℚ p) with hGzt

  have hχ' : HasConductorExponentAt ℚ p χ⁻¹ a := hasConductorExponentAt_inv hχ
  have hχu' : ‖(χ⁻¹ (uniformizerUnit ℚ p) : ℂ)‖ = 1 := by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hχu, inv_one]
  have hA1 := gauss_eval p ha hχ' hχu' hz
  rw [inv_inv_char] at hA1
  have hA2 := gauss_eval p ha hχω hχωu hzt

  have hB := LanglandsTunnell.TateLocal.stdRootNumberAt_mul_stdRootNumberAt_inv_eq_apply_neg_one ℚ p χ a ha hχ hχu
  have hNa : halfPow p a ≠ 0 := halfPow_ne_zero p a
  have hεχω : stdRootNumberAt ℚ p (χ * ω) ≠ 0 :=
    LanglandsTunnell.TateLocal.stdRootNumberAt_ne_zero_of_hasConductorExponentAt ℚ p (χ * ω) a ha hχω hχωu

  rw [charExt_coe_units] at hA1 hA2

  apply mul_right_cancel₀ hNa

  have e1 : -tu * ztu = ϖ ^ m₀ := by
    rw [hztu, neg_mul_neg, mul_left_comm, mul_inv_cancel, mul_one]
  have e2 : ((ω (-tu) : ℂˣ) : ℂ) * ((ω ztu : ℂˣ) : ℂ) = ((ω ϖ : ℂˣ) : ℂ) ^ m₀ := by
    rw [← Units.val_mul, ← map_mul, e1, map_zpow, Units.val_zpow_eq_zpow_val]
  have e3 : ((χ ztu : ℂˣ) : ℂ) = ((χ (-1) : ℂˣ) : ℂ) * (((χ ϖ : ℂˣ) : ℂ) ^ m₀ * (((χ tu : ℂˣ) : ℂ))⁻¹) := by
    rw [hztu, ← neg_one_mul, map_mul, map_mul, map_zpow, map_inv, Units.val_mul, Units.val_mul,
      Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val]
  have hunit' : ((((χ * ω) ϖ : ℂˣ) : ℂ)) ^ (-m₀) * ((ω (-tu) : ℂˣ) : ℂ) * (((χ * ω) ztu : ℂˣ) : ℂ)
      = ((χ (-1) : ℂˣ) : ℂ) * ((χ tu : ℂˣ) : ℂ)⁻¹ := by
    have hA : ((χ ϖ : ℂˣ) : ℂ) ^ m₀ ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
    have hBne : ((ω ϖ : ℂˣ) : ℂ) ^ m₀ ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
    have hT : ((χ tu : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have hm1 : ((χ (-1) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul, mul_zpow, zpow_neg, zpow_neg,
      e3, mul_assoc, mul_assoc, ← mul_assoc ((ω (-tu) : ℂˣ) : ℂ), mul_comm ((ω (-tu) : ℂˣ) : ℂ),
      mul_assoc _ ((ω (-tu) : ℂˣ) : ℂ), e2]
    field_simp
  have hzu' : ((χ zu : ℂˣ) : ℂ) = ((χ ϖ : ℂˣ) : ℂ) ^ n₀ * ((χ tu : ℂˣ) : ℂ) := by
    rw [hzu, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val]
  have hχinv : ((χ⁻¹ zu : ℂˣ) : ℂ) = (((χ zu : ℂˣ) : ℂ))⁻¹ := by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]

  calc (((χ * ω) ϖ : ℂˣ) : ℂ) ^ (-m₀) * ((ω (-tu) : ℂˣ) : ℂ) * Gzt * halfPow p a
      = (((χ * ω) ϖ : ℂˣ) : ℂ) ^ (-m₀) * ((ω (-tu) : ℂˣ) : ℂ) * (Gzt * halfPow p a) := by ring
    _ = (((χ * ω) ϖ : ℂˣ) : ℂ) ^ (-m₀) * ((ω (-tu) : ℂˣ) : ℂ) * ((((χ * ω) ztu : ℂˣ) : ℂ))
          * stdRootNumberAt ℚ p (χ * ω) := by rw [hA2]; ring
    _ = ((χ (-1) : ℂˣ) : ℂ) * ((χ tu : ℂˣ) : ℂ)⁻¹ * stdRootNumberAt ℚ p (χ * ω) := by rw [hunit']
    _ = stdRootNumberAt ℚ p (χ * ω) * ((χ ϖ : ℂˣ) : ℂ) ^ n₀
          * ((((χ zu : ℂˣ) : ℂ))⁻¹ * (stdRootNumberAt ℚ p χ * stdRootNumberAt ℚ p χ⁻¹)) := by
        rw [hB, hzu', mul_inv]
        have h0 : ((χ ϖ : ℂˣ) : ℂ) ^ n₀ ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
        field_simp
    _ = stdRootNumberAt ℚ p (χ * ω) * stdRootNumberAt ℚ p χ * (((χ ϖ : ℂˣ) : ℂ) ^ n₀
          * ((((χ⁻¹ zu : ℂˣ) : ℂ)) * stdRootNumberAt ℚ p χ⁻¹)) := by rw [hχinv]; ring
    _ = stdRootNumberAt ℚ p (χ * ω) * stdRootNumberAt ℚ p χ * (((χ ϖ : ℂˣ) : ℂ) ^ n₀ * (Gz * halfPow p a)) := by
        rw [hA1]
    _ = stdRootNumberAt ℚ p (χ * ω) * stdRootNumberAt ℚ p χ * (((χ ϖ : ℂˣ) : ℂ) ^ n₀ * Gz) * halfPow p a := by
        ring

end GaussIdentity

end AutomorphicForm.WhittakerModel.TorusShellCore
p2m_reactivate "P2MW.S_AutomorphicForm_WhittakerModel_exists_torusShell_eq_zero_and_torusShell_dual_eq_stdRootNumberAt_mul_of_mem_localLevelOne_top.AutomorphicForm P2MW.S_AutomorphicForm_WhittakerModel_exists_torusShell_eq_zero_and_torusShell_dual_eq_stdRootNumberAt_mul_of_mem_localLevelOne_top.AutomorphicForm.WhittakerModel P2MW.S_AutomorphicForm_WhittakerModel_exists_torusShell_eq_zero_and_torusShell_dual_eq_stdRootNumberAt_mul_of_mem_localLevelOne_top.AutomorphicForm.WhittakerModel.TorusShellCore"
p2m_reactivate "P2MW.S_AutomorphicForm_WhittakerModel_exists_torusShell_eq_zero_and_torusShell_dual_eq_stdRootNumberAt_mul_of_mem_localLevelOne_top.AutomorphicForm P2MW.S_AutomorphicForm_WhittakerModel_exists_torusShell_eq_zero_and_torusShell_dual_eq_stdRootNumberAt_mul_of_mem_localLevelOne_top.AutomorphicForm.WhittakerModel"
p2m_reactivate "P2MW.S_AutomorphicForm_WhittakerModel_exists_torusShell_eq_zero_and_torusShell_dual_eq_stdRootNumberAt_mul_of_mem_localLevelOne_top.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_WhittakerModel_exists_torusShell_eq_zero_and_torusShell_dual_eq_stdRootNumberAt_mul_of_mem_localLevelOne_top.AutomorphicForm P2MW.S_AutomorphicForm_WhittakerModel_exists_torusShell_eq_zero_and_torusShell_dual_eq_stdRootNumberAt_mul_of_mem_localLevelOne_top.AutomorphicForm.WhittakerModel P2MW.S_AutomorphicForm_WhittakerModel_exists_torusShell_eq_zero_and_torusShell_dual_eq_stdRootNumberAt_mul_of_mem_localLevelOne_top.AutomorphicForm.WhittakerModel.TorusShellCore"

set_option maxHeartbeats 6400000 in
open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker NumberField.AdelicLevel NumberField.StandardAddChar AutomorphicForm.WhittakerModel.TorusShellCore in

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (c : ℕ)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ c), ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω z : ℂˣ) : ℂ) * w₂base g)
    (hωu : ‖(ω (uniformizerUnit ℚ p) : ℂ)‖ = 1)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (a : ℕ)
    (hχ : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p χ a)
    (hχu : ‖(χ (uniformizerUnit ℚ p) : ℂ)‖ = 1)
    (hdeep : 2 * c + 1 ≤ a)
    (wJ : GL (Fin 2) (p.adicCompletion ℚ))
    (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0])
    (k : GL (Fin 2) (p.adicCompletion ℚ)) (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤)
    (t : p.adicCompletion ℚ) :
    letI := localBorel ℚ p
    LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (χ * ω) a ∧
    ∃ n₁ n₂ : ℤ,
      (∀ n : ℤ, n < n₁ ∨ n₂ < n →
        (∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
            w₂base (diagOne (uniformizerUnit ℚ p ^ n * u) * unipotent t * k) * ((χ u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) = 0) ∧
      (∀ m : ℤ, m < -n₂ - 2 * a ∨ -n₁ - 2 * a < m →
        (∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
            w₂base (diagOne (uniformizerUnit ℚ p ^ m * u) * wJ * unipotent t * k) *
              (((χ * ω)⁻¹ u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) = 0) ∧
      ∀ m : ℤ,
        (((χ * ω) (uniformizerUnit ℚ p) : ℂˣ) : ℂ) ^ (-m) *
            (∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
              w₂base (diagOne (uniformizerUnit ℚ p ^ m * u) * wJ * unipotent t * k) *
                (((χ * ω)⁻¹ u : ℂˣ) : ℂ)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
          LanglandsTunnell.TateLocal.stdRootNumberAt ℚ p (χ * ω) *
              LanglandsTunnell.TateLocal.stdRootNumberAt ℚ p χ *
            ((((χ (uniformizerUnit ℚ p) : ℂˣ) : ℂ) ^ (-m - 2 * a)) *
              ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
                w₂base (diagOne (uniformizerUnit ℚ p ^ (-m - 2 * a) * u) * unipotent t * k) *
                  ((χ u : ℂˣ) : ℂ)
                ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) := by
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  have hwJ' : wJ = weylJ := eq_weylJ_of_coe hwJ
  subst hwJ'

  show HasConductorExponentAt ℚ p (χ * ω) a ∧ ∃ n₁ n₂ : ℤ,
      (∀ n : ℤ, n < n₁ ∨ n₂ < n → (∫ u in USet p, w₂base (diagOne (uniformizerUnit ℚ p ^ n * u) * unipotent t * k)
        * ((χ u : ℂˣ) : ℂ) ∂(mulHaar p)) = 0) ∧
      (∀ m : ℤ, m < -n₂ - 2 * a ∨ -n₁ - 2 * a < m → (∫ u in USet p,
        w₂base (diagOne (uniformizerUnit ℚ p ^ m * u) * weylJ * unipotent t * k) * (((χ * ω)⁻¹ u : ℂˣ) : ℂ)
          ∂(mulHaar p)) = 0) ∧
      ∀ m : ℤ, (((χ * ω) (uniformizerUnit ℚ p) : ℂˣ) : ℂ) ^ (-m) * (∫ u in USet p,
          w₂base (diagOne (uniformizerUnit ℚ p ^ m * u) * weylJ * unipotent t * k) * (((χ * ω)⁻¹ u : ℂˣ) : ℂ)
            ∂(mulHaar p)) =
        stdRootNumberAt ℚ p (χ * ω) * stdRootNumberAt ℚ p χ * ((((χ (uniformizerUnit ℚ p) : ℂˣ) : ℂ) ^ (-m - 2 * a))
          * ∫ u in USet p, w₂base (diagOne (uniformizerUnit ℚ p ^ (-m - 2 * a) * u) * unipotent t * k)
            * ((χ u : ℂˣ) : ℂ) ∂(mulHaar p))
  set ϖ : (p.adicCompletion ℚ)ˣ := uniformizerUnit ℚ p with hϖ

  obtain ⟨hψ0, hψ0'⟩ := psi_level_data p
  have hψ1 : ∃ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ psiLocal ℚ p x ≠ 1 := by
    simpa using hψ0'

  have hca : c + 1 ≤ a := by omega
  have ha : 1 ≤ a := by omega
  have hωc : ∀ u ∈ higherUnitsAt ℚ p c, ω u = 1 :=
    central_eq_one_of_mem_higherUnitsAt w₂base c hw₂K hw₂ne ω hcentral
  have hχω : HasConductorExponentAt ℚ p (χ * ω) a :=
    hasConductorExponentAt_mul_of_forall_mem_higherUnitsAt χ ω a c hχ hωc hca
  have hχt : HasConductorExponentAt ℚ p (χ * ω)⁻¹ a := hasConductorExponentAt_inv hχω
  have hχωu : ‖(((χ * ω) ϖ : ℂˣ) : ℂ)‖ = 1 := by
    rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hϖ, hχu, hωu, mul_one]
  refine ⟨hχω, ?_⟩

  obtain ⟨cχu, hcχ⟩ :=
    LanglandsTunnell.TateLocal.exists_forall_mem_higherUnitsAt_apply_eq_psiLocal_mul_sub_one_of_hasConductorExponentAt
      ℚ p χ a hχ
  set cχ : p.adicCompletion ℚ := (cχu : p.adicCompletion ℚ) with hcχdef
  have hcχ' : ∀ u ∈ higherUnitsAt ℚ p (hDepth a), ((χ u : ℂˣ) : ℂ) = psiLocal ℚ p (cχ * ((u : p.adicCompletion ℚ) - 1)) :=
    hcχ
  have hct : ∀ u ∈ higherUnitsAt ℚ p (hDepth a),
      (((χ * ω)⁻¹ u : ℂˣ) : ℂ) = psiLocal ℚ p (-cχ * ((u : p.adicCompletion ℚ) - 1)) := by
    intro u hu
    have hh : c ≤ hDepth a := by unfold hDepth; omega
    have hωu1 : ω u = 1 := hωc u (higherUnitsAt_antitone ℚ p hh hu)
    rw [MonoidHom.inv_apply, MonoidHom.mul_apply, hωu1, mul_one, Units.val_inv_eq_inv_val, hcχ' u hu, neg_mul,
      AddChar.map_neg_eq_inv]

  by_cases ht1 : Valued.v t ≤ 1
  · have hkA : unipotent t * k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := Subgroup.mul_mem _ (unipotent_mem_top ht1) hk
    have hkB : weylJ * unipotent t * k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ weylJ_mem_top (unipotent_mem_top ht1)) hk
    have hs0 : ∀ n : ℤ, Valued.v (((ϖ ^ n : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * 0) ≠ WithZero.exp (a : ℤ) := by
      intro n; rw [mul_zero, map_zero]; exact WithZero.exp_ne_zero.symm
    have hCall : ∀ n : ℤ, (∫ u in USet p, w₂base (diagOne (ϖ ^ n * u) * unipotent t * k) * ((χ u : ℂˣ) : ℂ)
        ∂(mulHaar p)) = 0 := by
      intro n
      have h := shellIntegral_eq_zero_of_valued_ne p w₂base c hw₂K hkA χ a ha hca hχ (ϖ ^ n) 0 (hs0 n)
      rw [← h]
      refine setIntegral_congr_fun (measurableSet_USet p) fun u _ => ?_
      simp only [mul_zero, AddChar.map_zero_eq_one, one_mul, mul_assoc]
    have hDall : ∀ m : ℤ, (∫ u in USet p, w₂base (diagOne (ϖ ^ m * u) * weylJ * unipotent t * k)
        * (((χ * ω)⁻¹ u : ℂˣ) : ℂ) ∂(mulHaar p)) = 0 := by
      intro m
      have h := shellIntegral_eq_zero_of_valued_ne p w₂base c hw₂K hkB (χ * ω)⁻¹ a ha hca hχt (ϖ ^ m) 0 (hs0 m)
      rw [← h]
      refine setIntegral_congr_fun (measurableSet_USet p) fun u _ => ?_
      simp only [mul_zero, AddChar.map_zero_eq_one, one_mul, mul_assoc]
    refine ⟨0, -1, fun n _ => hCall n, fun m _ => hDall m, fun m => ?_⟩
    rw [hDall, hCall, mul_zero, mul_zero, mul_zero]

  have ht0 : t ≠ 0 := by
    intro h; apply ht1; rw [h, map_zero]; exact zero_le'
  set tu : (p.adicCompletion ℚ)ˣ := Units.mk0 t ht0 with htu
  have htu' : (tu : p.adicCompletion ℚ) = t := Units.val_mk0 ht0
  have hvt0 : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).mpr ht0
  obtain ⟨e, he⟩ : ∃ e : ℤ, Valued.v t = WithZero.exp e := ⟨_, (WithZero.exp_log hvt0).symm⟩
  have he1 : 1 ≤ e := by
    rw [not_le, he, ← WithZero.exp_zero, WithZero.exp_lt_exp] at ht1; omega
  have hvtu : Valued.v (tu : p.adicCompletion ℚ) = WithZero.exp e := by rw [htu']; exact he
  have hvtui : Valued.v ((tu⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = WithZero.exp (-e) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hvtu, WithZero.exp_neg]
  set n₀ : ℤ := e - a with hn₀
  set m₀ : ℤ := -e - a with hm₀

  obtain ⟨kB, hkBdef⟩ : ∃ kB : GL (Fin 2) (p.adicCompletion ℚ),
      kB = lowerUni ((tu⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * k := ⟨_, rfl⟩
  have hkB : kB ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
    rw [hkBdef]
    refine Subgroup.mul_mem _ (lowerUni_mem_top ?_) hk
    rw [hvtui, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega

  have hR1 : ∀ y : (p.adicCompletion ℚ)ˣ, w₂base (diagOne y * unipotent t * k)
      = psiLocal ℚ p ((y : p.adicCompletion ℚ) * t) * w₂base (diagOne y * k) := by
    intro y
    rw [diagOne_mul_unipotent, mul_assoc, hw₂law]

  obtain ⟨y₁, hy₁⟩ : ∃ y₁ : (p.adicCompletion ℚ)ˣ, y₁ = tu⁻¹ ^ 2 := ⟨_, rfl⟩
  have hunip : (unipotent t : GL (Fin 2) (p.adicCompletion ℚ)) = unipotent ((tu : p.adicCompletion ℚ)) := by
    rw [htu']
  have hR2 : ∀ y : (p.adicCompletion ℚ)ˣ, w₂base (diagOne y * weylJ * unipotent t * k)
      = ((ω (-tu) : ℂˣ) : ℂ) * (psiLocal ℚ p ((y : p.adicCompletion ℚ) * -((tu⁻¹ : (p.adicCompletion ℚ)ˣ) :
          p.adicCompletion ℚ)) * w₂base (diagOne (y * y₁) * kB)) := by
    intro y
    have hmat : diagOne y * weylJ * unipotent t * k
        = Matrix.GeneralLinearGroup.scalar (Fin 2) (-tu) *
          (unipotent ((y : p.adicCompletion ℚ) * -((tu⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) *
            (diagOne (y * y₁) * kB)) := by
      rw [hunip, diagOne_mul_weylJ_mul_unipotent, hy₁, hkBdef]
      simp only [mul_assoc]
    rw [hmat, hcentral, hw₂law]

  have hC : ∀ n : ℤ, (∫ u in USet p, w₂base (diagOne (ϖ ^ n * u) * unipotent t * k) * ((χ u : ℂˣ) : ℂ)
      ∂(mulHaar p)) = ∫ u in USet p, psiLocal ℚ p (((ϖ ^ n * u : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * t)
        * w₂base (diagOne (ϖ ^ n * u) * k) * ((χ u : ℂˣ) : ℂ) ∂(mulHaar p) := by
    intro n
    refine setIntegral_congr_fun (measurableSet_USet p) fun u _ => ?_
    simp only [hR1]
  have hD : ∀ m : ℤ, (∫ u in USet p, w₂base (diagOne (ϖ ^ m * u) * weylJ * unipotent t * k)
      * (((χ * ω)⁻¹ u : ℂˣ) : ℂ) ∂(mulHaar p))
      = ((ω (-tu) : ℂˣ) : ℂ) * ∫ u in USet p,
          psiLocal ℚ p (((ϖ ^ m * y₁ * u : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * -t)
            * w₂base (diagOne (ϖ ^ m * y₁ * u) * kB) * (((χ * ω)⁻¹ u : ℂˣ) : ℂ) ∂(mulHaar p) := by
    intro m
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_USet p) fun u _ => ?_
    simp only [hR2]
    have hyy : ϖ ^ m * u * y₁ = ϖ ^ m * y₁ * u := mul_right_comm _ _ _
    have hψarg : ((ϖ ^ m * u : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * -((tu⁻¹ : (p.adicCompletion ℚ)ˣ) :
        p.adicCompletion ℚ) = ((ϖ ^ m * y₁ * u : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * -t := by
      rw [hy₁, ← htu']
      push_cast
      field_simp
    rw [hyy, hψarg]
    ring

  have hvC : ∀ n : ℤ, Valued.v (((ϖ ^ n : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * t) = WithZero.exp (e - n) := by
    intro n; rw [map_mul, hϖ, valued_uniformizerUnit_zpow, he, ← WithZero.exp_add]; congr 1; ring
  have hvy₁ : Valued.v ((y₁ : p.adicCompletion ℚ)) = WithZero.exp (-(2 * e)) := by
    rw [hy₁, Units.val_pow_eq_pow_val, map_pow, hvtui, ← WithZero.exp_nsmul]; congr 1; ring
  have hvD : ∀ m : ℤ, Valued.v (((ϖ ^ m * y₁ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * -t)
      = WithZero.exp (-m - e) := by
    intro m
    rw [Units.val_mul, map_mul, map_mul, Valuation.map_neg, hϖ, valued_uniformizerUnit_zpow, hvy₁, he,
      ← WithZero.exp_add, ← WithZero.exp_add]
    congr 1; ring

  have hCz : ∀ n : ℤ, n ≠ n₀ → (∫ u in USet p, w₂base (diagOne (ϖ ^ n * u) * unipotent t * k) * ((χ u : ℂˣ) : ℂ)
      ∂(mulHaar p)) = 0 := by
    intro n hn
    rw [hC]
    refine shellIntegral_eq_zero_of_valued_ne p w₂base c hw₂K hk χ a ha hca hχ (ϖ ^ n) t ?_
    rw [hvC]
    exact fun h => hn (by have := WithZero.exp_injective h; omega)
  have hDz : ∀ m : ℤ, m ≠ m₀ → (∫ u in USet p, w₂base (diagOne (ϖ ^ m * u) * weylJ * unipotent t * k)
      * (((χ * ω)⁻¹ u : ℂˣ) : ℂ) ∂(mulHaar p)) = 0 := by
    intro m hm
    rw [hD, shellIntegral_eq_zero_of_valued_ne p w₂base c hw₂K hkB (χ * ω)⁻¹ a ha hca hχt (ϖ ^ m * y₁) (-t) ?_,
      mul_zero]
    rw [hvD]
    exact fun h => hm (by have := WithZero.exp_injective h; omega)

  by_cases heac : e + c + 1 ≤ (a : ℤ)
  · have hCall : ∀ n : ℤ, (∫ u in USet p, w₂base (diagOne (ϖ ^ n * u) * unipotent t * k) * ((χ u : ℂˣ) : ℂ)
        ∂(mulHaar p)) = 0 := by
      intro n
      by_cases hn : n = n₀
      · rw [hC]
        refine (setIntegral_congr_fun (measurableSet_USet p) fun u hu => ?_).trans (integral_zero _ _)
        have hu1 : Valued.v (u : p.adicCompletion ℚ) = 1 := hu
        have hzero : w₂base (diagOne (ϖ ^ n * u) * k) = 0 := by
          refine profile_eq_zero_of_le_valued w₂base c hw₂K (psiLocal ℚ p) hw₂law hψ1 hk (ϖ ^ n * u) ?_
          rw [Units.val_mul, map_mul, hu1, mul_one, hϖ, valued_uniformizerUnit_zpow, WithZero.exp_le_exp, hn]
          omega
        simp only [hzero, mul_zero, zero_mul]
      · exact hCz n hn
    have hDall : ∀ m : ℤ, (∫ u in USet p, w₂base (diagOne (ϖ ^ m * u) * weylJ * unipotent t * k)
        * (((χ * ω)⁻¹ u : ℂˣ) : ℂ) ∂(mulHaar p)) = 0 := by
      intro m
      by_cases hm : m = m₀
      · rw [hD]
        refine (congrArg _ ((setIntegral_congr_fun (measurableSet_USet p) fun u hu => ?_).trans
          (integral_zero _ _))).trans (mul_zero _)
        have hu1 : Valued.v (u : p.adicCompletion ℚ) = 1 := hu
        have hzero : w₂base (diagOne (ϖ ^ m * y₁ * u) * kB) = 0 := by
          refine profile_eq_zero_of_le_valued w₂base c hw₂K (psiLocal ℚ p) hw₂law hψ1 hkB (ϖ ^ m * y₁ * u) ?_
          rw [Units.val_mul, map_mul, hu1, mul_one, Units.val_mul, map_mul, hϖ, valued_uniformizerUnit_zpow, hvy₁,
            ← WithZero.exp_add, WithZero.exp_le_exp, hm]
          omega
        simp only [hzero, mul_zero, zero_mul]
      · exact hDz m hm
    refine ⟨0, -1, fun n _ => hCall n, fun m _ => hDall m, fun m => ?_⟩
    rw [hDall, hCall, mul_zero, mul_zero, mul_zero]

  have hec : (c : ℤ) ≤ e := by omega
  refine ⟨n₀, n₀, fun n hn => hCz n (by omega), fun m hm => hDz m (by omega), fun m => ?_⟩
  by_cases hmm : m = m₀
  swap
  · rw [hDz m hmm, hCz (-m - 2 * a) (by omega), mul_zero, mul_zero, mul_zero]
  subst hmm
  have hnm : -m₀ - 2 * (a : ℤ) = n₀ := by omega
  rw [hnm]

  have hkBk : ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * kB) = w₂base (g * k) := by
    intro g
    rw [hkBdef, ← mul_assoc]
    refine profile_lowerUni w₂base c hw₂K hk ?_ g
    rw [hvtui, WithZero.exp_le_exp]; omega

  have hz : Valued.v (((ϖ ^ n₀ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * t) = WithZero.exp (a : ℤ) := by
    rw [hvC]; congr 1; omega
  obtain ⟨u₁, hu₁, hgood⟩ := exists_good_unit p ha hχ hχu cχ hcχ' hz

  have hCval := shellIntegral_eq_apply_mul p w₂base c hw₂K hk χ a hdeep hχ cχ hcχ' (ϖ ^ n₀) t hz u₁ hu₁ hgood

  set y₀ : (p.adicCompletion ℚ)ˣ := ϖ ^ m₀ * y₁ with hy₀
  have hu₁0 : u₁ ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hu₁]; exact one_ne_zero)
  set u₂ : p.adicCompletion ℚ := ((ϖ ^ n₀ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * u₁
    * ((y₀⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) with hu₂
  have hzt : Valued.v (((y₀ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * -t) = WithZero.exp (a : ℤ) := by
    rw [hy₀, hvD]; congr 1; omega
  have hvy₀ : Valued.v ((y₀ : p.adicCompletion ℚ)) = WithZero.exp (-m₀ - 2 * e) := by
    rw [hy₀, Units.val_mul, map_mul, hϖ, valued_uniformizerUnit_zpow, hvy₁, ← WithZero.exp_add]
    congr 1
  have hu₂v : Valued.v u₂ = 1 := by
    rw [hu₂, map_mul, map_mul, hu₁, mul_one, hϖ, valued_uniformizerUnit_zpow, Units.val_inv_eq_inv_val, map_inv₀,
      hvy₀, ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_zero]
    congr 1; omega
  have hy₀u₂ : (y₀ : p.adicCompletion ℚ) * u₂ = ((ϖ ^ n₀ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * u₁ := by
    rw [hu₂, Units.val_inv_eq_inv_val]
    field_simp
  have hgood₂ : Valued.v ((y₀ : p.adicCompletion ℚ) * -t * u₂ + -cχ) ≤ WithZero.exp ((hDepth a : ℕ) : ℤ) := by
    have : (y₀ : p.adicCompletion ℚ) * -t * u₂ + -cχ
        = -(((ϖ ^ n₀ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * t * u₁ + cχ) := by
      rw [mul_right_comm, hy₀u₂]; ring
    rw [this, Valuation.map_neg]
    exact hgood
  have hDval := shellIntegral_eq_apply_mul p w₂base c hw₂K hkB (χ * ω)⁻¹ a hdeep hχt (-cχ) hct y₀ (-t) hzt u₂ hu₂v hgood₂

  have hPP : profileExt p w₂base kB ((y₀ : p.adicCompletion ℚ) * u₂)
      = profileExt p w₂base k (((ϖ ^ n₀ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * u₁) := by
    rw [hy₀u₂]
    unfold profileExt
    split_ifs with h
    · rfl
    · exact hkBk _

  have hzform : ((ϖ ^ n₀ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * t
      = ((ϖ ^ n₀ * tu : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) := by rw [Units.val_mul, htu']
  have hztform : (y₀ : p.adicCompletion ℚ) * -t
      = (((-(ϖ ^ m₀ * tu⁻¹) : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ) := by
    have htune : (tu : p.adicCompletion ℚ) ≠ 0 := tu.ne_zero
    have hϖne : (ϖ : p.adicCompletion ℚ) ≠ 0 := ϖ.ne_zero
    rw [hy₀, hy₁, ← htu']
    push_cast
    field_simp
  have hzu : Valued.v (((ϖ ^ n₀ * tu : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ) = WithZero.exp (a : ℤ) := by
    rw [← hzform]; exact hz
  have hztu : Valued.v (((-(ϖ ^ m₀ * tu⁻¹) : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ) = WithZero.exp (a : ℤ) := by
    rw [← hztform]; exact hzt
  have hGI := gauss_identity p χ ω a ha hχ hχω hχu hχωu tu n₀ m₀ (by omega) hzu hztu

  rw [hD m₀, hDval, hC n₀, hCval, hPP, hzform, hztform]
  rw [← hzform] at hGI ⊢
  rw [← hztform] at hGI ⊢
  set P := profileExt p w₂base k (((ϖ ^ n₀ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * u₁)
  set Gz := ∫ x in UF p, psiLocal ℚ p (((ϖ ^ n₀ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * t * x) * charExt χ x
    ∂(selfDualHaarAt ℚ p)
  set Gzt := ∫ x in UF p, psiLocal ℚ p ((y₀ : p.adicCompletion ℚ) * -t * x) * charExt (χ * ω)⁻¹ x
    ∂(selfDualHaarAt ℚ p)
  calc (((χ * ω) ϖ : ℂˣ) : ℂ) ^ (-m₀) * (((ω (-tu) : ℂˣ) : ℂ) * (P * Gzt))
      = P * ((((χ * ω) ϖ : ℂˣ) : ℂ) ^ (-m₀) * ((ω (-tu) : ℂˣ) : ℂ) * Gzt) := by ring
    _ = P * (stdRootNumberAt ℚ p (χ * ω) * stdRootNumberAt ℚ p χ * (((χ ϖ : ℂˣ) : ℂ) ^ n₀ * Gz)) := by rw [hGI]
    _ = stdRootNumberAt ℚ p (χ * ω) * stdRootNumberAt ℚ p χ * (((χ ϖ : ℂˣ) : ℂ) ^ n₀ * (P * Gz)) := by ring

end S_AutomorphicForm_WhittakerModel_exists_torusShell_eq_zero_and_torusShell_dual_eq_stdRootNumberAt_mul_of_mem_localLevelOne_top
end P2MW
export P2MW.S_AutomorphicForm_WhittakerModel_exists_torusShell_eq_zero_and_torusShell_dual_eq_stdRootNumberAt_mul_of_mem_localLevelOne_top (solution)
