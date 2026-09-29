-- Prove2me | solution 1 for AutomorphicForm.WhittakerModel.exists_torusZeta_dual_eq_stdRootNumberAt_mul_stdRootNumberAt_mul_of_admissible_of_le_of_norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/26b7b805-c884-55b6-bbbd-78eb626a321a

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_torusShell_eq_zero_and_torusShell_dual_eq_stdRootNumberAt_mul_of_mem_span
import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_norm_diagOne_mul_le_of_irreducible_admissible
import Theorems.Thm_LanglandsTunnell_TateLocal_integrable_and_hasSum_setIntegral_shell_of_isLocallyConstant_of_norm_le
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_WhittakerModel_exists_torusZeta_dual_eq_stdRootNumberAt_mul_stdRootNumberAt_mul_of_admissible_of_le_of_norm_eq_one
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker NumberField.AdelicLevel NumberField.StandardAddChar Topology

open scoped NNReal ENNReal

namespace AutomorphicForm
p2m_export "AutomorphicForm" "WhittakerModel.exists_torusShell_eq_zero_and_torusShell_dual_eq_stdRootNumberAt_mul_of_mem_span WhittakerModel.exists_norm_diagOne_mul_le_of_irreducible_admissible"
namespace WhittakerModel
p2m_export "AutomorphicForm.WhittakerModel" "exists_torusShell_eq_zero_and_torusShell_dual_eq_stdRootNumberAt_mul_of_mem_span exists_norm_diagOne_mul_le_of_irreducible_admissible"
namespace TorusZetaFE
p2m_open "AutomorphicForm.WhittakerModel AutomorphicForm"

section GLtwo

variable {F : Type*} [Field F]

def gl2 (a b c d : F) (h : a * d - b * c ≠ 0) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; c, d] (by rwa [Matrix.det_fin_two_of])

@[scoped simp] theorem gl2_coe (a b c d : F) (h : a * d - b * c ≠ 0) :
    ((gl2 a b c d h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] := rfl

def weylJ : GL (Fin 2) F := gl2 0 1 (-1) 0 (by simp)

theorem weylJ_coe : ((weylJ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl

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

theorem weylJ_inv : (weylJ : GL (Fin 2) F)⁻¹ = gl2 0 (-1) 1 0 (by simp) := by
  rw [inv_eq_iff_mul_eq_one]
  apply gl_eq_of_entries <;> simp [mul_coe_apply, weylJ_coe]

theorem diagOne_coe (a : Fˣ) :
    ((AdelicLevel.diagOne a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![(a : F), 0; 0, 1] := by
  ext i j
  rw [AdelicLevel.diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

end GLtwo

section Level

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

theorem isLocalLevelOne_top_of_entries (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
    (h : ∀ i j, Valued.v (m i j) ≤ 1) : AdelicDock.IsLocalLevelOne (𝓞 K) K v ⊤ m := by
  refine ⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (h i j), ?_, ?_⟩
  · rw [AdelicLevel.idealBound_top]; exact h 1 0
  · rw [AdelicLevel.idealBound_top]
    exact (Valuation.map_sub _ _ _).trans (max_le (h 1 1) (by rw [Valuation.map_one]))

theorem weylJ_mem_top : (weylJ : GL (Fin 2) (v.adicCompletion K)) ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤ := by
  rw [AdelicDock.mem_localLevelOne_iff, weylJ_inv]
  constructor <;> refine isLocalLevelOne_top_of_entries _ fun i j => ?_ <;>
    fin_cases i <;> fin_cases j <;> simp [weylJ_coe]

end Level

section Padic

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem valued_uniformizerUnit_zpow (m : ℤ) :
    Valued.v ((uniformizerUnit ℚ p ^ m : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = WithZero.exp (-m) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

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
    {y : p.adicCompletion ℚ | Valued.v y = 1} = {y : p.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (0 : ℤ)}
          \ {y : p.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (-(1 : ℤ))} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_diff]
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

theorem isClosed_UF : IsClosed {y : p.adicCompletion ℚ | Valued.v y = 1} := by
  rw [UF_eq_diff]
  exact (isClosed_ball p _).sdiff (isOpen_ball p _)

theorem isCompact_UF : IsCompact {y : p.adicCompletion ℚ | Valued.v y = 1} := by
  have hint : IsCompact {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp 0} := by
    have : ((p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ))) = {x | Valued.v x ≤ WithZero.exp 0} := by
      ext x
      rw [WithZero.exp_zero]
      exact HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p
    rw [← this]
    exact isCompact_iff_compactSpace.mpr (show CompactSpace (p.adicCompletionIntegers ℚ) from inferInstance)
  refine hint.of_isClosed_subset (isClosed_UF p) fun u hu => ?_
  have hu' : Valued.v u = 1 := hu
  show Valued.v u ≤ WithZero.exp 0
  rw [hu', WithZero.exp_zero]

theorem isCompact_USet : IsCompact {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1} := by
  rw [Units.isEmbedding_val₀.isCompact_iff]
  have : Units.val '' {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1}
      = {u : p.adicCompletion ℚ | Valued.v u = 1} := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · intro hx
      have hx0 : x ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hx]; exact one_ne_zero)
      exact ⟨Units.mk0 x hx0, hx, rfl⟩
  rw [this]
  exact isCompact_UF p

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  set c : ℝ≥0 := (Ideal.absNorm p.asIdeal : ℝ≥0) ^ (-(addCharLevel (psiLocal ℚ p) : ℝ) / 2) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot))).ne'
  have hdef : selfDualHaarAt ℚ p = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

theorem continuous_diagOne : Continuous (AdelicLevel.diagOne : (p.adicCompletion ℚ)ˣ → GL (Fin 2) (p.adicCompletion ℚ)) := by
  have key : ∀ f : (p.adicCompletion ℚ)ˣ → (p.adicCompletion ℚ)ˣ, Continuous (fun y => ((f y : (p.adicCompletion ℚ)ˣ) :
      p.adicCompletion ℚ)) → Continuous fun y : (p.adicCompletion ℚ)ˣ =>
        ((AdelicLevel.diagOne (f y) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) := by
    intro f hf
    refine continuous_matrix fun i j => ?_
    have : (fun y : (p.adicCompletion ℚ)ˣ => ((AdelicLevel.diagOne (f y) : GL (Fin 2) (p.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j) = fun y => !![((f y : (p.adicCompletion ℚ)ˣ) :
          p.adicCompletion ℚ), 0; 0, 1] i j := by
      funext y; rw [diagOne_coe]
    rw [this]
    fin_cases i <;> fin_cases j
    · simpa using hf
    · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero,
        Matrix.cons_val_fin_one]
      exact continuous_const
    · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      exact continuous_const
    · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact continuous_const
  rw [Units.continuous_iff]
  refine ⟨key id Units.continuous_val, ?_⟩
  have : (fun y : (p.adicCompletion ℚ)ˣ => (((AdelicLevel.diagOne y : GL (Fin 2) (p.adicCompletion ℚ))⁻¹ :
      GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)))
      = fun y => ((AdelicLevel.diagOne y⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2)
        (p.adicCompletion ℚ)) := by
    funext y; rw [map_inv]
  rw [this]
  exact key (fun y => y⁻¹) Units.continuous_coe_inv

theorem isLocallyConstant_char {η : (p.adicCompletion ℚ)ˣ →* ℂˣ} {b : ℕ} (hη : ∀ u ∈ higherUnitsAt ℚ p b, η u = 1) :
    IsLocallyConstant fun y : (p.adicCompletion ℚ)ˣ => ((η y : ℂˣ) : ℂ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y₀
  have hcont : Continuous fun y : (p.adicCompletion ℚ)ˣ =>
      ((y * y₀⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) - 1 :=
    (Units.continuous_val.comp (continuous_mul_const y₀⁻¹)).sub continuous_const
  have hball : IsOpen {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-((b : ℤ) + 1))} := isOpen_ball p _
  have hmem : (fun y : (p.adicCompletion ℚ)ˣ => ((y * y₀⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) - 1) ⁻¹'
      {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-((b : ℤ) + 1))} ∈ 𝓝 y₀ := by
    refine (hball.preimage hcont).mem_nhds ?_
    show Valued.v (((y₀ * y₀⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) - 1) ≤ _
    rw [mul_inv_cancel, Units.val_one, sub_self, map_zero]; exact zero_le'
  refine Filter.mem_of_superset hmem fun y hy => ?_
  have hy' : Valued.v (((y * y₀⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-((b : ℤ) + 1)) :=
    hy
  have hval : Valued.v ((y * y₀⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = 1 := by
    have hlt : Valued.v (((y * y₀⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) - 1)
        < Valued.v (1 : p.adicCompletion ℚ) := by
      rw [map_one, ← WithZero.exp_zero]
      exact hy'.trans_lt (WithZero.exp_lt_exp.mpr (by omega))
    have := Valuation.map_eq_of_sub_lt _ hlt
    rwa [map_one] at this
  have hmemU : y * y₀⁻¹ ∈ higherUnitsAt ℚ p b := by
    refine (mem_higherUnitsAt_iff ℚ p).mpr ⟨hval, ?_⟩
    rcases Nat.eq_zero_or_pos b with h0 | hpos
    · exact Or.inl h0
    · exact Or.inr (hy'.trans (WithZero.exp_le_exp.mpr (by omega)))
  show ((η y : ℂˣ) : ℂ) = ((η y₀ : ℂˣ) : ℂ)
  rw [show y = (y * y₀⁻¹) * y₀ by rw [inv_mul_cancel_right], map_mul, hη _ hmemU, one_mul]

end Padic

section Laurent

open Polynomial

theorem Icc_eq_image (n₁ n₂ : ℤ) :
    Finset.Icc n₁ n₂ = (Finset.range (n₂ - n₁ + 1).toNat).image fun j : ℕ => n₁ + j := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(n - n₁).toNat, ?_, ?_⟩ <;> omega
  · rintro ⟨j, hj, rfl⟩
    omega

theorem sum_Icc_cpow_mul_eq (N : ℂ) (hN : N ≠ 0) (n₁ n₂ : ℤ) (f : ℤ → ℂ) (s : ℂ) :
    ∑ n ∈ Finset.Icc n₁ n₂, N ^ (-((n : ℂ) * s)) * f n
      = N ^ (((-n₁ : ℤ) : ℂ) * s) *
        (∑ j ∈ Finset.range (n₂ - n₁ + 1).toNat, C (f (n₁ + j)) * X ^ j).eval (N ^ (-s)) := by
  rw [Icc_eq_image, Finset.sum_image (fun j₁ _ j₂ _ h => by simpa using h), eval_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X, ← Complex.cpow_nat_mul, mul_left_comm, ← Complex.cpow_add _ _ hN,
    mul_comm (f _)]
  congr 2
  push_cast
  ring

end Laurent

end AutomorphicForm.WhittakerModel.TorusZetaFE
p2m_reactivate "P2MW.S_AutomorphicForm_WhittakerModel_exists_torusZeta_dual_eq_stdRootNumberAt_mul_stdRootNumberAt_mul_of_admissible_of_le_of_norm_eq_one.AutomorphicForm P2MW.S_AutomorphicForm_WhittakerModel_exists_torusZeta_dual_eq_stdRootNumberAt_mul_stdRootNumberAt_mul_of_admissible_of_le_of_norm_eq_one.AutomorphicForm.WhittakerModel P2MW.S_AutomorphicForm_WhittakerModel_exists_torusZeta_dual_eq_stdRootNumberAt_mul_stdRootNumberAt_mul_of_admissible_of_le_of_norm_eq_one.AutomorphicForm.WhittakerModel.TorusZetaFE"
p2m_reactivate "P2MW.S_AutomorphicForm_WhittakerModel_exists_torusZeta_dual_eq_stdRootNumberAt_mul_stdRootNumberAt_mul_of_admissible_of_le_of_norm_eq_one.AutomorphicForm P2MW.S_AutomorphicForm_WhittakerModel_exists_torusZeta_dual_eq_stdRootNumberAt_mul_stdRootNumberAt_mul_of_admissible_of_le_of_norm_eq_one.AutomorphicForm.WhittakerModel"
p2m_reactivate "P2MW.S_AutomorphicForm_WhittakerModel_exists_torusZeta_dual_eq_stdRootNumberAt_mul_stdRootNumberAt_mul_of_admissible_of_le_of_norm_eq_one.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_WhittakerModel_exists_torusZeta_dual_eq_stdRootNumberAt_mul_stdRootNumberAt_mul_of_admissible_of_le_of_norm_eq_one.AutomorphicForm P2MW.S_AutomorphicForm_WhittakerModel_exists_torusZeta_dual_eq_stdRootNumberAt_mul_stdRootNumberAt_mul_of_admissible_of_le_of_norm_eq_one.AutomorphicForm.WhittakerModel P2MW.S_AutomorphicForm_WhittakerModel_exists_torusZeta_dual_eq_stdRootNumberAt_mul_stdRootNumberAt_mul_of_admissible_of_le_of_norm_eq_one.AutomorphicForm.WhittakerModel.TorusZetaFE"

set_option maxHeartbeats 6400000 in
open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker NumberField.AdelicLevel NumberField.StandardAddChar AutomorphicForm.WhittakerModel.TorusZetaFE Polynomial in

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (c : ℕ)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ c), ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ
        (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          w₂base (g * h)),
      w ≠ 0 →
        w₂base ∈
          Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
            fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hadm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
            fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) →
            W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω z : ℂˣ) : ℂ) * w₂base g)
    (hωu : ‖(ω (uniformizerUnit ℚ p) : ℂ)‖ = 1)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (a : ℕ)
    (hχ : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p χ a)
    (hχu : ‖(χ (uniformizerUnit ℚ p) : ℂ)‖ = 1)
    (hdeep : 2 * c + 1 ≤ a)
    (wJ : GL (Fin 2) (p.adicCompletion ℚ))
    (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0]) :
    letI := localBorel ℚ p
    ∀ w ∈ Submodule.span ℂ
        (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((ω y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((ω y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (χ * ω) a ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (LanglandsTunnell.TateLocal.stdRootNumberAt ℚ p (χ * ω) *
                (((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ a) *
              (LanglandsTunnell.TateLocal.stdRootNumberAt ℚ p χ *
                (((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ a) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))) := by
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI : (selfDualHaarAt ℚ p).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt p
  have hwJ' : wJ = weylJ := eq_weylJ_of_coe hwJ
  subst hwJ'
  intro w hw

  obtain ⟨hχω, hE⟩ :=
    AutomorphicForm.WhittakerModel.exists_torusShell_eq_zero_and_torusShell_dual_eq_stdRootNumberAt_mul_of_mem_span
      p w₂base hw₂law c hw₂K hw₂ne ω hcentral hωu χ a hχ hχu hdeep weylJ rfl
  obtain ⟨hlc, -, n₁, n₂, hA, hB, hI⟩ := hE w hw

  have hstabGen : ∀ (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      ∀ W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
        fun g : GL (Fin 2) (p.adicCompletion ℚ) => f (g * h)),
      ∀ h : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * h)) ∈ Submodule.span ℂ
        (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => f (g * h)) := by
    intro f W hW h
    induction hW using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h', rfl⟩ := hx
      exact Submodule.subset_span ⟨h * h', funext fun g => by simp only [mul_assoc]⟩
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul r x _ hx => exact Submodule.smul_mem _ r hx
  set V := Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
    fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)) with hV
  have hstab : ∀ W ∈ V, ∀ h : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * h)) ∈ V := hstabGen w₂base
  have hlaw : ∀ W ∈ V, ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      W (unipotent x * g) = psiLocal ℚ p x * W g := by
    intro W hW x g
    induction hW using Submodule.span_induction with
    | mem W' hW' =>
      obtain ⟨h, rfl⟩ := hW'
      show w₂base (unipotent x * g * h) = psiLocal ℚ p x * w₂base (g * h)
      rw [mul_assoc, hw₂law]
    | zero => simp
    | add W₁ W₂ _ _ h₁ h₂ => simp only [Pi.add_apply, h₁, h₂, mul_add]
    | smul r W' _ h => simp only [Pi.smul_apply, smul_eq_mul, h]; ring
  have hKopen : IsOpen (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ c) : Set (GL (Fin 2) (p.adicCompletion ℚ))) :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p (p.asIdeal ^ c) (pow_ne_zero _ p.ne_bot)).2
  have hsm : ∀ W ∈ V, ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
      IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
        W (g * k) = W g := by
    intro W hW
    induction hW using Submodule.span_induction with
    | mem W' hW' =>
      obtain ⟨h, rfl⟩ := hW'
      refine ⟨(AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ c)).comap (MulAut.conj h⁻¹).toMonoidHom, ?_, ?_⟩
      · have hc' : Continuous fun k : GL (Fin 2) (p.adicCompletion ℚ) => h⁻¹ * k * h⁻¹⁻¹ :=
          (continuous_const.mul continuous_id).mul continuous_const
        exact hKopen.preimage hc'
      · intro k hk g
        have hk' : h⁻¹ * k * h⁻¹⁻¹ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ c) := hk
        show w₂base (g * k * h) = w₂base (g * h)
        rw [← hw₂K _ hk' (g * h)]
        congr 1
        group
    | zero => exact ⟨⊤, isOpen_univ, fun k _ g => rfl⟩
    | add W₁ W₂ _ _ h₁ h₂ =>
      obtain ⟨U₁, hU₁, hk₁⟩ := h₁
      obtain ⟨U₂, hU₂, hk₂⟩ := h₂
      refine ⟨U₁ ⊓ U₂, hU₁.inter hU₂, fun k hk g => ?_⟩
      simp only [Pi.add_apply, hk₁ k hk.1, hk₂ k hk.2]
    | smul r W' _ h =>
      obtain ⟨U, hU, hk⟩ := h
      exact ⟨U, hU, fun k hk' g => by simp only [Pi.smul_apply, hk k hk']⟩
  have hirr : ∀ W₀ ∈ V, W₀ ≠ 0 → ∀ W ∈ V, W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h)) := by
    intro W₀ hW₀ hne W hW
    have hb := hw₂irr W₀ hW₀ hne
    have hle : V ≤ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
        fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h)) := by
      rw [hV, Submodule.span_le]
      rintro _ ⟨h, rfl⟩
      exact hstabGen W₀ w₂base hb h
    exact hle hW
  have hcenV : ∀ W ∈ V, ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      W (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω z : ℂˣ) : ℂ) * W g := fun W hW => (hE W hW).2.1

  obtain ⟨Cst, M, c₀, -, -, hbound⟩ :=
    AutomorphicForm.WhittakerModel.exists_norm_diagOne_mul_le_of_irreducible_admissible p V hstab hlaw hsm hadm hirr
      ω hcenV w hw
  have hφC : ∀ y : (p.adicCompletion ℚ)ˣ, ‖w (diagOne y)‖ ≤ Cst * max 1 ((modulus (y : p.adicCompletion ℚ)) ^ M)⁻¹ :=
    fun y => by simpa only [mul_one] using (hbound y 1 (Subgroup.one_mem _)).1
  have hφc₀ : ∀ y : (p.adicCompletion ℚ)ˣ, c₀ < modulus (y : p.adicCompletion ℚ) → w (diagOne y) = 0 :=
    fun y hy => by simpa only [mul_one] using (hbound y 1 (Subgroup.one_mem _)).2 hy
  have hφtC : ∀ y : (p.adicCompletion ℚ)ˣ,
      ‖w (diagOne y * weylJ)‖ ≤ Cst * max 1 ((modulus (y : p.adicCompletion ℚ)) ^ M)⁻¹ :=
    fun y => (hbound y weylJ weylJ_mem_top).1
  have hφtc₀ : ∀ y : (p.adicCompletion ℚ)ˣ, c₀ < modulus (y : p.adicCompletion ℚ) → w (diagOne y * weylJ) = 0 :=
    fun y hy => (hbound y weylJ weylJ_mem_top).2 hy
  have hφlc : IsLocallyConstant fun y : (p.adicCompletion ℚ)ˣ => w (diagOne y) :=
    hlc.comp_continuous (continuous_diagOne p)
  have hφtlc : IsLocallyConstant fun y : (p.adicCompletion ℚ)ˣ => w (diagOne y * weylJ) :=
    hlc.comp_continuous ((continuous_diagOne p).mul continuous_const)
  have hχlc : IsLocallyConstant fun y : (p.adicCompletion ℚ)ˣ => ((χ y : ℂˣ) : ℂ) := isLocallyConstant_char p hχ.1
  have hχtlc : IsLocallyConstant fun y : (p.adicCompletion ℚ)ˣ => (((χ * ω)⁻¹ y : ℂˣ) : ℂ) := by
    refine isLocallyConstant_char p (b := a) fun u hu => ?_
    rw [MonoidHom.inv_apply, hχω.1 u hu, inv_one]
  obtain ⟨Bχ, hBχ⟩ := (isCompact_USet p).exists_bound_of_continuousOn hχlc.continuous.continuousOn
  obtain ⟨Bt, hBt⟩ := (isCompact_USet p).exists_bound_of_continuousOn hχtlc.continuous.continuousOn
  have hχtu : ‖(((χ * ω)⁻¹ (uniformizerUnit ℚ p) : ℂˣ) : ℂ)‖ = 1 := by
    rw [MonoidHom.inv_apply, MonoidHom.mul_apply, Units.val_inv_eq_inv_val, norm_inv, Units.val_mul, norm_mul,
      hχu, hωu, mul_one, inv_one]
  have hre₁ : ∀ s : ℂ, (M : ℝ) + 1 / 2 < s.re → (M : ℝ) < (s - 1 / 2).re := by
    intro s hs
    rw [Complex.sub_re, Complex.div_re]
    norm_num
    linarith
  have hre₂ : ∀ s : ℂ, s.re < 1 / 2 - M → (M : ℝ) < (1 / 2 - s).re := by
    intro s hs
    rw [Complex.sub_re, Complex.div_re]
    norm_num
    linarith
  have SCK := fun (s : ℂ) (hs : (M : ℝ) + 1 / 2 < s.re) =>
    LanglandsTunnell.TateLocal.integrable_and_hasSum_setIntegral_shell_of_isLocallyConstant_of_norm_le ℚ p
      (selfDualHaarAt ℚ p) (fun y => w (diagOne y)) hφlc Cst M hφC c₀ hφc₀ χ hχlc Bχ (fun u hu => hBχ u hu) hχu
      (s - 1 / 2) (hre₁ s hs)
  have SCD := fun (s : ℂ) (hs : s.re < 1 / 2 - M) =>
    LanglandsTunnell.TateLocal.integrable_and_hasSum_setIntegral_shell_of_isLocallyConstant_of_norm_le ℚ p
      (selfDualHaarAt ℚ p) (fun y => w (diagOne y * weylJ)) hφtlc Cst M hφtC c₀ hφtc₀ (χ * ω)⁻¹ hχtlc Bt
      (fun u hu => hBt u hu) hχtu (1 / 2 - s) (hre₂ s hs)

  set N : ℂ := (Ideal.absNorm p.asIdeal : ℂ) with hN
  have hN0 : N ≠ 0 := by
    rw [hN]; exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot
  set ϖ := uniformizerUnit ℚ p with hϖ
  set cK : ℤ → ℂ := fun n => ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
    w (diagOne (ϖ ^ n * u)) * ((χ u : ℂˣ) : ℂ) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) with hcK
  set cD : ℤ → ℂ := fun m => ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
    w (diagOne (ϖ ^ m * u) * weylJ) * (((χ * ω)⁻¹ u : ℂˣ) : ℂ) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
    with hcD
  set f : ℤ → ℂ := fun n => N ^ ((n : ℂ) / 2) * ((χ ϖ : ℂˣ) : ℂ) ^ n * cK n with hf
  set g : ℤ → ℂ := fun j => N ^ ((j : ℂ) / 2) * (((χ * ω)⁻¹ ϖ : ℂˣ) : ℂ) ^ (-j) * cD (-j) with hg
  set P : Polynomial ℂ := ∑ j ∈ Finset.range (n₂ - n₁ + 1).toNat, C (f (n₁ + j)) * X ^ j with hP
  set Pd : Polynomial ℂ := ∑ j ∈ Finset.range ((n₂ + 2 * a) - (n₁ + 2 * a) + 1).toNat,
    C (g ((n₁ + 2 * a) + j)) * X ^ j with hPd

  have hfun : ∀ s : ℂ, (fun y : (p.adicCompletion ℚ)ˣ =>
      w (diagOne y * weylJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((ω y : ℂˣ) : ℂ))⁻¹ *
        ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
      = fun y => (fun y => w (diagOne y * weylJ)) y * (((χ * ω)⁻¹ y : ℂˣ) : ℂ) *
        ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s) := by
    intro s
    funext y
    rw [MonoidHom.inv_apply, MonoidHom.mul_apply, mul_inv, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_inv_eq_inv_val]
    ring

  have hKsum : ∀ s : ℂ, (M : ℝ) + 1 / 2 < s.re →
      (∫ y : (p.adicCompletion ℚ)ˣ, w (diagOne y) * ((χ y : ℂˣ) : ℂ) *
          ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))))
        = ∑ n ∈ Finset.Icc n₁ n₂, N ^ (-((n : ℂ) * s)) * f n := by
    intro s hs
    have hsum := (SCK s hs).2.2
    have hfin : HasSum (fun n : ℤ => N ^ (-((n : ℂ) * (s - 1 / 2))) * ((χ ϖ : ℂˣ) : ℂ) ^ n * cK n)
        (∑ n ∈ Finset.Icc n₁ n₂, N ^ (-((n : ℂ) * (s - 1 / 2))) * ((χ ϖ : ℂˣ) : ℂ) ^ n * cK n) := by
      refine hasSum_sum_of_ne_finset_zero fun n hn => ?_
      rw [Finset.mem_Icc] at hn
      rw [hcK]
      simp only
      rw [hA n (by omega), mul_zero]
    rw [hsum.unique hfin]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hf]
    simp only
    rw [show -((n : ℂ) * (s - 1 / 2)) = -((n : ℂ) * s) + (n : ℂ) / 2 by ring, Complex.cpow_add _ _ hN0]
    ring

  have hDsum : ∀ s : ℂ, s.re < 1 / 2 - M →
      (∫ y : (p.adicCompletion ℚ)ˣ, (fun y => w (diagOne y * weylJ)) y * (((χ * ω)⁻¹ y : ℂˣ) : ℂ) *
          ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))))
        = ∑ j ∈ Finset.Icc (n₁ + 2 * a) (n₂ + 2 * a), N ^ (-((j : ℂ) * s)) * g j := by
    intro s hs
    have hsum := (SCD s hs).2.2
    have hfin : HasSum (fun m : ℤ => N ^ (-((m : ℂ) * (1 / 2 - s))) * (((χ * ω)⁻¹ ϖ : ℂˣ) : ℂ) ^ m * cD m)
        (∑ m ∈ Finset.Icc (-n₂ - 2 * a) (-n₁ - 2 * a),
          N ^ (-((m : ℂ) * (1 / 2 - s))) * (((χ * ω)⁻¹ ϖ : ℂˣ) : ℂ) ^ m * cD m) := by
      refine hasSum_sum_of_ne_finset_zero fun m hm => ?_
      rw [Finset.mem_Icc] at hm
      rw [hcD]
      simp only
      rw [hB m (by omega), mul_zero]
    rw [hsum.unique hfin]
    have hS : Finset.Icc (-n₂ - 2 * (a : ℤ)) (-n₁ - 2 * a) = (Finset.Icc (n₁ + 2 * (a : ℤ)) (n₂ + 2 * a)).image
        fun j : ℤ => -j := by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_image]
      constructor
      · intro h; exact ⟨-m, by omega, by omega⟩
      · rintro ⟨j, hj, rfl⟩; omega
    rw [hS, Finset.sum_image fun x _ y _ h => neg_injective h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hg]
    simp only
    push_cast
    rw [show -(-(j : ℂ) * (1 / 2 - s)) = -((j : ℂ) * s) + (j : ℂ) / 2 by ring, Complex.cpow_add _ _ hN0]
    ring

  have hPeval : ∀ s : ℂ, ∑ n ∈ Finset.Icc n₁ n₂, N ^ (-((n : ℂ) * s)) * f n
      = N ^ (((-n₁ : ℤ) : ℂ) * s) * P.eval (N ^ (-s)) := fun s => sum_Icc_cpow_mul_eq N hN0 n₁ n₂ f s
  have hPdeval : ∀ s : ℂ, ∑ j ∈ Finset.Icc (n₁ + 2 * a) (n₂ + 2 * a), N ^ (-((j : ℂ) * s)) * g j
      = N ^ (((-(n₁ + 2 * a) : ℤ) : ℂ) * s) * Pd.eval (N ^ (-s)) := fun s =>
    sum_Icc_cpow_mul_eq N hN0 (n₁ + 2 * a) (n₂ + 2 * a) g s

  have hχω0 : (((χ * ω) ϖ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have key : ∀ (s : ℂ) (n : ℤ), N ^ (-(((n + 2 * (a : ℤ) : ℤ) : ℂ) * s)) * g (n + 2 * a)
      = stdRootNumberAt ℚ p (χ * ω) * (N ^ ((1 : ℂ) / 2 - s)) ^ a *
          (stdRootNumberAt ℚ p χ * (N ^ ((1 : ℂ) / 2 - s)) ^ a) * (N ^ (-((n : ℂ) * s)) * f n) := by
    intro s n
    have hI' := hI (-(n + 2 * a))
    have hidx : -(-(n + 2 * (a : ℤ))) - 2 * (a : ℤ) = n := by ring
    rw [hidx, neg_neg] at hI'
    rw [hg, hf]
    simp only
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_zpow', neg_neg]
    calc N ^ (-(((n + 2 * (a : ℤ) : ℤ) : ℂ) * s)) *
          (N ^ (((n + 2 * (a : ℤ) : ℤ) : ℂ) / 2) * (((χ * ω) ϖ : ℂˣ) : ℂ) ^ (n + 2 * a) * cD (-(n + 2 * a)))
        = N ^ (-(((n + 2 * (a : ℤ) : ℤ) : ℂ) * s)) * N ^ (((n + 2 * (a : ℤ) : ℤ) : ℂ) / 2)
          * ((((χ * ω) ϖ : ℂˣ) : ℂ) ^ (n + 2 * a) * cD (-(n + 2 * a))) := by ring
      _ = N ^ (-(((n + 2 * (a : ℤ) : ℤ) : ℂ) * s)) * N ^ (((n + 2 * (a : ℤ) : ℤ) : ℂ) / 2)
          * (stdRootNumberAt ℚ p (χ * ω) * stdRootNumberAt ℚ p χ * (((χ ϖ : ℂˣ) : ℂ) ^ n * cK n)) := by
            rw [hI']
      _ = _ := by
            rw [← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hN0]
            have hpow : N ^ (-(((n + 2 * (a : ℤ) : ℤ) : ℂ) * s) + ((n + 2 * (a : ℤ) : ℤ) : ℂ) / 2)
                = N ^ ((a : ℂ) * (1 / 2 - s)) * N ^ ((a : ℂ) * (1 / 2 - s)) * N ^ (-((n : ℂ) * s)) * N ^ ((n : ℂ) / 2) := by
              rw [← Complex.cpow_add _ _ hN0, ← Complex.cpow_add _ _ hN0, ← Complex.cpow_add _ _ hN0]
              congr 1
              push_cast
              ring
            rw [hpow]
            ring

  refine ⟨P, Pd, -n₁, -(n₁ + 2 * a), (M : ℝ) + 1 / 2, 1 / 2 - M, fun s hs => (SCK s hs).1, fun s hs => ?_,
    fun s hs => ?_, fun s hs => ?_, hχω, fun s => ?_⟩
  · rw [hKsum s hs, hPeval s]
  · rw [hfun s]; exact (SCD s hs).1
  · rw [hfun s, hDsum s hs, hPdeval s]
  · rw [← hPdeval s, ← hPeval s, Finset.mul_sum]
    have hS : Finset.Icc (n₁ + 2 * (a : ℤ)) (n₂ + 2 * a) = (Finset.Icc n₁ n₂).image fun n : ℤ => n + 2 * a := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_image]
      constructor
      · intro h; exact ⟨j - 2 * a, by omega, by omega⟩
      · rintro ⟨n, hn, rfl⟩; omega
    rw [hS, Finset.sum_image fun x _ y _ h => add_right_cancel h]
    exact Finset.sum_congr rfl fun n _ => key s n

end S_AutomorphicForm_WhittakerModel_exists_torusZeta_dual_eq_stdRootNumberAt_mul_stdRootNumberAt_mul_of_admissible_of_le_of_norm_eq_one
end P2MW
export P2MW.S_AutomorphicForm_WhittakerModel_exists_torusZeta_dual_eq_stdRootNumberAt_mul_stdRootNumberAt_mul_of_admissible_of_le_of_norm_eq_one (solution)
