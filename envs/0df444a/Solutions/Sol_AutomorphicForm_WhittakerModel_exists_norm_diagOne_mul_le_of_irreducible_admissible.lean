-- Prove2me | solution 1 for AutomorphicForm.WhittakerModel.exists_norm_diagOne_mul_le_of_irreducible_admissible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/3430bb80-9b12-5246-bb8a-1afa51d8c839

import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_NumberField_StandardAddChar_psiLocal_rat_eq_psiV
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_WhittakerModel_exists_norm_diagOne_mul_le_of_irreducible_admissible
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

open IsDedekindDomain NumberField
open scoped WithZero Pointwise

namespace KirillovBound

section Valuation

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem exists_uniformizer :
    ∃ ϖ : v.adicCompletion K, Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer K v
  exact ⟨((WithVal.equiv (HeightOneSpectrum.valuation K v)).symm π : v.adicCompletion K),
    by rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hπ⟩

variable {K v}

theorem uniformizer_ne_zero {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) :
    ϖ ≠ 0 := by
  intro h; rw [h, Valuation.map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm

theorem v_uniformizer_zpow {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (j : ℤ) : Valued.v (ϖ ^ j) = WithZero.exp (-j) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem v_uniformizer_pow {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (n : ℕ) : Valued.v (ϖ ^ n) = WithZero.exp (-(n : ℤ)) := by
  rw [← zpow_natCast, v_uniformizer_zpow hϖ]

theorem v_add_le {x y : v.adicCompletion K} {γ : ℤᵐ⁰} (hx : Valued.v x ≤ γ) (hy : Valued.v y ≤ γ) :
    Valued.v (x + y) ≤ γ :=
  (Valuation.map_add _ x y).trans (max_le hx hy)

theorem v_sub_le {x y : v.adicCompletion K} {γ : ℤᵐ⁰} (hx : Valued.v x ≤ γ) (hy : Valued.v y ≤ γ) :
    Valued.v (x - y) ≤ γ := by
  rw [sub_eq_add_neg]; exact v_add_le hx (by rwa [Valuation.map_neg])

theorem v_mul_le {x y : v.adicCompletion K} {a b : ℤ} (hx : Valued.v x ≤ WithZero.exp a)
    (hy : Valued.v y ≤ WithZero.exp b) : Valued.v (x * y) ≤ WithZero.exp (a + b) := by
  rw [Valuation.map_mul, WithZero.exp_add]
  exact mul_le_mul' hx hy

theorem exp_neg_succ_lt_one (n : ℕ) : WithZero.exp (-((n : ℤ) + 1)) < (1 : ℤᵐ⁰) := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega

theorem exp_neg_succ_le_one (n : ℕ) : WithZero.exp (-((n : ℤ) + 1)) ≤ (1 : ℤᵐ⁰) :=
  (exp_neg_succ_lt_one n).le

theorem exp_antitone_succ (n : ℕ) :
    WithZero.exp (-(((n + 1 : ℕ) : ℤ) + 1)) ≤ WithZero.exp (-((n : ℤ) + 1)) := by
  rw [WithZero.exp_le_exp]; push_cast; omega

theorem v_lt_one_iff (x : v.adicCompletion K) :
    Valued.v x < 1 ↔ Valued.v x ≤ WithZero.exp (-1 : ℤ) := by
  by_cases hx : Valued.v x = 0
  · simp [hx]
  · rw [← WithZero.exp_log hx, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

theorem eq_zero_of_forall_v_le (x : v.adicCompletion K)
    (h : ∀ n : ℕ, Valued.v x ≤ WithZero.exp (-((n : ℤ) + 1))) : x = 0 := by
  by_contra hx
  have hx' : Valued.v x ≠ 0 := by rwa [ne_eq, Valuation.zero_iff]
  set L := WithZero.log (Valued.v x) with hL
  have hxL : Valued.v x = WithZero.exp L := (WithZero.exp_log hx').symm
  have := h ((-L).toNat)
  rw [hxL, WithZero.exp_le_exp] at this
  omega

theorem v_eq_one_of_sub_one {x : v.adicCompletion K} {n : ℕ}
    (hx : Valued.v (x - 1) ≤ WithZero.exp (-((n : ℤ) + 1))) : Valued.v x = 1 := by
  have : x = 1 + (x - 1) := by ring
  rw [this]
  exact Valuation.map_one_add_of_lt _ (hx.trans_lt (exp_neg_succ_lt_one n))

theorem ne_zero_of_v_eq_one {x : v.adicCompletion K} (hx : Valued.v x = 1) : x ≠ 0 := by
  intro h; rw [h, Valuation.map_zero] at hx; exact zero_ne_one hx

theorem v_inv_sub_one {x : v.adicCompletion K} {n : ℕ}
    (hx : Valued.v (x - 1) ≤ WithZero.exp (-((n : ℤ) + 1))) :
    Valued.v (x⁻¹ - 1) ≤ WithZero.exp (-((n : ℤ) + 1)) := by
  have h1 := v_eq_one_of_sub_one hx
  have hx0 := ne_zero_of_v_eq_one h1
  have : x⁻¹ - 1 = x⁻¹ * (-(x - 1)) := by field_simp; ring
  rw [this, Valuation.map_mul, Valuation.map_neg, map_inv₀, h1, inv_one, one_mul]
  exact hx

theorem isOpen_ball (m : ℤ) : IsOpen {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp m} := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer K v
  have hϖ0 : ϖ ≠ 0 := uniformizer_ne_zero hϖ
  have hset : {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp m} =
      (fun x => ϖ ^ m * x) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, v_uniformizer_zpow hϖ,
      WithZero.exp_neg]
    constructor
    · intro h
      calc (WithZero.exp m)⁻¹ * Valued.v x ≤ (WithZero.exp m)⁻¹ * WithZero.exp m :=
            mul_le_mul_right h _
        _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
    · intro h
      calc Valued.v x = WithZero.exp m * ((WithZero.exp m)⁻¹ * Valued.v x) := by
            rw [← mul_assoc, mul_inv_cancel₀ WithZero.exp_ne_zero, one_mul]
        _ ≤ WithZero.exp m * 1 := mul_le_mul_right h _
        _ = WithZero.exp m := mul_one _
  rw [hset]
  exact (Valued.isOpen_valuationSubring _).preimage (continuous_const_mul _)

theorem exists_eq_zpow_mul (ϖ : v.adicCompletion K) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (y : v.adicCompletion K) (hy : y ≠ 0) :
    ∃ (j : ℤ) (t : v.adicCompletion K), Valued.v t = 1 ∧ y = ϖ ^ j * t ∧
      Valued.v y = WithZero.exp (-j) := by
  have hϖ0 : ϖ ≠ 0 := uniformizer_ne_zero hϖ
  have hy' : Valued.v y ≠ 0 := by rwa [ne_eq, Valuation.zero_iff]
  set L := WithZero.log (Valued.v y) with hL
  have hyL : Valued.v y = WithZero.exp L := (WithZero.exp_log hy').symm
  refine ⟨-L, ϖ ^ L * y, ?_, ?_, ?_⟩
  · rw [Valuation.map_mul, v_uniformizer_zpow hϖ, hyL, ← WithZero.exp_add, neg_add_cancel,
      WithZero.exp_zero]
  · rw [zpow_neg, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ hϖ0), one_mul]
  · rw [neg_neg, hyL]

end Valuation

section GLtwo

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => HeightOneSpectrum.adicCompletion K v
local notation "Mat" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)
local notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)

def gl2 (a b c d : F) (h : a * d - b * c ≠ 0) : G :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; c, d] (by rwa [Matrix.det_fin_two_of])

@[scoped simp] theorem gl2_coe (a b c d : F) (h : a * d - b * c ≠ 0) :
    ((gl2 a b c d h : G) : Mat) = !![a, b; c, d] := rfl

theorem unipotent_coe (x : F) :
    ((UnramifiedWhittaker.unipotent x : G) : Mat) = !![1, x; 0, 1] := rfl

theorem diagOne_coe (a : Fˣ) :
    ((AdelicLevel.diagOne a : G) : Mat) = !![(a : F), 0; 0, 1] := by
  ext i j
  rw [AdelicLevel.diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem gl_eq_of_entries {g h : G}
    (h00 : (g : Mat) 0 0 = (h : Mat) 0 0) (h01 : (g : Mat) 0 1 = (h : Mat) 0 1)
    (h10 : (g : Mat) 1 0 = (h : Mat) 1 0) (h11 : (g : Mat) 1 1 = (h : Mat) 1 1) : g = h := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem mul_coe_apply (g h : G) (i j : Fin 2) :
    ((g * h : G) : Mat) i j = (g : Mat) i 0 * (h : Mat) 0 j + (g : Mat) i 1 * (h : Mat) 1 j := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem unipotent_mul (x y : F) :
    (UnramifiedWhittaker.unipotent x : G) * UnramifiedWhittaker.unipotent y =
      UnramifiedWhittaker.unipotent (x + y) := by
  apply gl_eq_of_entries <;> simp [mul_coe_apply, unipotent_coe] <;> ring

theorem unipotent_zero : (UnramifiedWhittaker.unipotent (0 : F) : G) = 1 := by
  apply gl_eq_of_entries <;> simp [unipotent_coe]

theorem diagOne_mul_unipotent (a : Fˣ) (x : F) :
    (AdelicLevel.diagOne a : G) * UnramifiedWhittaker.unipotent x =
      UnramifiedWhittaker.unipotent ((a : F) * x) * AdelicLevel.diagOne a := by
  apply gl_eq_of_entries <;> simp [mul_coe_apply, unipotent_coe, diagOne_coe]

theorem diag_mul_unipotent (t₁ t₂ : F) (h : t₁ * t₂ - 0 * 0 ≠ 0) (x : F) :
    gl2 t₁ 0 0 t₂ h * UnramifiedWhittaker.unipotent x =
      UnramifiedWhittaker.unipotent (t₁ * x * t₂⁻¹) * gl2 t₁ 0 0 t₂ h := by
  have ht₂ : t₂ ≠ 0 := by intro h'; apply h; simp [h']
  apply gl_eq_of_entries <;> simp [mul_coe_apply, unipotent_coe] ; field_simp

theorem iwahori_factor (k : G) (hα : (k : Mat) 0 0 ≠ 0) :
    ∃ (hL : (1 : F) * 1 - 0 * ((k : Mat) 1 0 / (k : Mat) 0 0) ≠ 0)
      (hD : (k : Mat) 0 0 * ((k : Mat) 1 1 - (k : Mat) 0 1 * (k : Mat) 1 0 / (k : Mat) 0 0) - 0 * 0 ≠ 0),
      k = gl2 1 0 ((k : Mat) 1 0 / (k : Mat) 0 0) 1 hL *
        gl2 ((k : Mat) 0 0) 0 0 ((k : Mat) 1 1 - (k : Mat) 0 1 * (k : Mat) 1 0 / (k : Mat) 0 0) hD *
        UnramifiedWhittaker.unipotent ((k : Mat) 0 1 / (k : Mat) 0 0) := by
  have hdet : (k : Mat).det ≠ 0 := (Matrix.GeneralLinearGroup.det_ne_zero k)
  rw [Matrix.det_fin_two] at hdet
  have hL : (1 : F) * 1 - 0 * ((k : Mat) 1 0 / (k : Mat) 0 0) ≠ 0 := by simp
  have hD : (k : Mat) 0 0 * ((k : Mat) 1 1 - (k : Mat) 0 1 * (k : Mat) 1 0 / (k : Mat) 0 0) - 0 * 0 ≠ 0 := by
    have : (k : Mat) 0 0 * ((k : Mat) 1 1 - (k : Mat) 0 1 * (k : Mat) 1 0 / (k : Mat) 0 0) - 0 * 0 =
        (k : Mat) 0 0 * (k : Mat) 1 1 - (k : Mat) 0 1 * (k : Mat) 1 0 := by field_simp; ring
    rw [this]; exact hdet
  refine ⟨hL, hD, ?_⟩
  apply gl_eq_of_entries <;> simp [mul_coe_apply, unipotent_coe] <;> field_simp <;> ring

theorem lower_mul_unipotent (c w : F) (hcw : 1 + c * w ≠ 0)
    (hL : (1 : F) * 1 - 0 * c ≠ 0)
    (hk : (1 - w / (1 + c * w) * c) * (1 + c * w) - 0 * c ≠ 0) :
    gl2 1 0 c 1 hL * UnramifiedWhittaker.unipotent w =
      UnramifiedWhittaker.unipotent (w / (1 + c * w)) *
        gl2 (1 - w / (1 + c * w) * c) 0 c (1 + c * w) hk := by
  have hcw' : 1 + w * c ≠ 0 := by rwa [mul_comm w c]
  apply gl_eq_of_entries <;> simp [mul_coe_apply, unipotent_coe] <;> field_simp <;> ring

def lvl (n : ℕ) : ℤᵐ⁰ := WithZero.exp (-((n : ℤ) + 1))

theorem lvl_le_one (n : ℕ) : lvl n ≤ 1 := exp_neg_succ_le_one n

theorem lvl_lt_one (n : ℕ) : lvl n < 1 := exp_neg_succ_lt_one n

theorem lvl_succ_le (n : ℕ) : lvl (n + 1) ≤ lvl n := exp_antitone_succ n

theorem v_mul_le_lvl_left {n : ℕ} {x y : F} (hx : Valued.v x ≤ lvl n) (hy : Valued.v y ≤ 1) :
    Valued.v (x * y) ≤ lvl n := by
  rw [Valuation.map_mul]; simpa using mul_le_mul' hx hy

theorem v_mul_le_lvl_right {n : ℕ} {x y : F} (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ lvl n) :
    Valued.v (x * y) ≤ lvl n := by
  rw [Valuation.map_mul]; simpa using mul_le_mul' hx hy

theorem v_le_one_of_sub_one_le {n : ℕ} {x : F} (hx : Valued.v (x - 1) ≤ lvl n) : Valued.v x ≤ 1 := by
  have : x = (x - 1) + 1 := by ring
  rw [this]; exact v_add_le (hx.trans (lvl_le_one n)) (by simp)

structure IsCong (n : ℕ) (m : Mat) : Prop where
  h00 : Valued.v (m 0 0 - 1) ≤ lvl n
  h01 : Valued.v (m 0 1) ≤ lvl n
  h10 : Valued.v (m 1 0) ≤ lvl n
  h11 : Valued.v (m 1 1 - 1) ≤ lvl n

theorem IsCong.v00 {n : ℕ} {m : Mat} (h : IsCong n m) : Valued.v (m 0 0) = 1 := v_eq_one_of_sub_one h.h00
theorem IsCong.v11 {n : ℕ} {m : Mat} (h : IsCong n m) : Valued.v (m 1 1) = 1 := v_eq_one_of_sub_one h.h11

theorem IsCong.integral {n : ℕ} {m : Mat} (h : IsCong n m) (i j : Fin 2) : Valued.v (m i j) ≤ 1 := by
  fin_cases i <;> fin_cases j
  · exact h.v00.le
  · exact h.h01.trans (lvl_le_one n)
  · exact h.h10.trans (lvl_le_one n)
  · exact h.v11.le

theorem isCong_one (n : ℕ) : IsCong n (1 : Mat) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

theorem IsCong.mul {n : ℕ} {a b : Mat} (ha : IsCong n a) (hb : IsCong n b) : IsCong n (a * b) := by
  have e00 : (a * b) 0 0 - 1 = (a 0 0 - 1) * b 0 0 + (b 0 0 - 1) + a 0 1 * b 1 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]; ring
  have e01 : (a * b) 0 1 = a 0 0 * b 0 1 + a 0 1 * b 1 1 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (a * b) 1 0 = a 1 0 * b 0 0 + a 1 1 * b 1 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (a * b) 1 1 - 1 = a 1 0 * b 0 1 + ((a 1 1 - 1) * b 1 1 + (b 1 1 - 1)) := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e00]
    exact v_add_le (v_add_le (v_mul_le_lvl_left ha.h00 hb.v00.le) hb.h00)
      (v_mul_le_lvl_left ha.h01 (hb.integral 1 0))
  · rw [e01]
    exact v_add_le (v_mul_le_lvl_right ha.v00.le hb.h01) (v_mul_le_lvl_left ha.h01 hb.v11.le)
  · rw [e10]
    exact v_add_le (v_mul_le_lvl_left ha.h10 hb.v00.le) (v_mul_le_lvl_right ha.v11.le hb.h10)
  · rw [e11]
    exact v_add_le (v_mul_le_lvl_left ha.h10 (hb.integral 0 1))
      (v_add_le (v_mul_le_lvl_left ha.h11 hb.v11.le) hb.h11)

theorem IsCong.v_det_sub_one {n : ℕ} {m : Mat} (h : IsCong n m) :
    Valued.v (m 0 0 * m 1 1 - m 0 1 * m 1 0 - 1) ≤ lvl n := by
  have : m 0 0 * m 1 1 - m 0 1 * m 1 0 - 1 = (m 0 0 - 1) * m 1 1 + (m 1 1 - 1) - m 0 1 * m 1 0 := by ring
  rw [this]
  exact v_sub_le (v_add_le (v_mul_le_lvl_left h.h00 h.v11.le) h.h11) (v_mul_le_lvl_left h.h01 (h.integral 1 0))

theorem IsCong.v_det {n : ℕ} {m : Mat} (h : IsCong n m) : Valued.v (m 0 0 * m 1 1 - m 0 1 * m 1 0) = 1 :=
  v_eq_one_of_sub_one h.v_det_sub_one

theorem IsCong.inv {n : ℕ} {g : G} (h : IsCong n (g : Mat)) : IsCong n ((g⁻¹ : G) : Mat) := by
  set D : F := (g : Mat) 0 0 * (g : Mat) 1 1 - (g : Mat) 0 1 * (g : Mat) 1 0 with hD
  have hvD : Valued.v D = 1 := h.v_det
  have hD0 : D ≠ 0 := ne_zero_of_v_eq_one hvD
  set B : Mat := !![(g : Mat) 1 1 / D, -(g : Mat) 0 1 / D; -(g : Mat) 1 0 / D, (g : Mat) 0 0 / D] with hB
  have hmul : (g : Mat) * B = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
  have hinv : ((g⁻¹ : G) : Mat) = B := by
    rw [Matrix.coe_units_inv, Matrix.inv_eq_right_inv hmul]
  have hvdiv : ∀ x : F, Valued.v (x / D) = Valued.v x := by
    intro x; rw [map_div₀, hvD, div_one]
  rw [hinv]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : B 0 0 - 1 = ((g : Mat) 1 1 - 1 - (D - 1)) / D := by
      simp only [B, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]
      field_simp; ring
    rw [this, hvdiv]
    exact v_sub_le h.h11 h.v_det_sub_one
  · have : B 0 1 = -(g : Mat) 0 1 / D := by simp [B]
    rw [this, hvdiv, Valuation.map_neg]; exact h.h01
  · have : B 1 0 = -(g : Mat) 1 0 / D := by simp [B]
    rw [this, hvdiv, Valuation.map_neg]; exact h.h10
  · have : B 1 1 - 1 = ((g : Mat) 0 0 - 1 - (D - 1)) / D := by
      simp only [B, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one]
      field_simp; ring
    rw [this, hvdiv]
    exact v_sub_le h.h00 h.v_det_sub_one

variable (K v) in

def congr (n : ℕ) : Subgroup G where
  carrier := {g | IsCong n (g : Mat)}
  one_mem' := by simpa using isCong_one n
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Matrix.GeneralLinearGroup.coe_mul] at *
    exact ha.mul hb
  inv_mem' := by
    intro g hg
    exact hg.inv

theorem mem_congr {n : ℕ} {g : G} : g ∈ congr K v n ↔ IsCong n (g : Mat) := Iff.rfl

theorem congr_antitone (n : ℕ) : congr K v (n + 1) ≤ congr K v n := by
  intro g hg
  exact ⟨hg.h00.trans (lvl_succ_le n), hg.h01.trans (lvl_succ_le n), hg.h10.trans (lvl_succ_le n),
    hg.h11.trans (lvl_succ_le n)⟩

theorem congr_antitone' {m n : ℕ} (h : m ≤ n) : congr K v n ≤ congr K v m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (congr_antitone _).trans ih

theorem isOpen_congr (n : ℕ) : IsOpen (congr K v n : Set G) := by
  have hc : ∀ i j : Fin 2, Continuous fun g : G => (g : Mat) i j := fun i j =>
    Units.continuous_val.matrix_elem i j
  have hball : IsOpen {x : F | Valued.v x ≤ lvl n} := isOpen_ball _
  have hball' : IsOpen {x : F | Valued.v (x - 1) ≤ lvl n} :=
    hball.preimage (continuous_id.sub continuous_const)
  have hset : (congr K v n : Set G) =
      ((fun g : G => (g : Mat) 0 0) ⁻¹' {x : F | Valued.v (x - 1) ≤ lvl n}) ∩
      ((fun g : G => (g : Mat) 0 1) ⁻¹' {x : F | Valued.v x ≤ lvl n}) ∩
      ((fun g : G => (g : Mat) 1 0) ⁻¹' {x : F | Valued.v x ≤ lvl n}) ∩
      ((fun g : G => (g : Mat) 1 1) ⁻¹' {x : F | Valued.v (x - 1) ≤ lvl n}) := by
    ext g
    simp only [SetLike.mem_coe, mem_congr, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨⟨⟨h.h00, h.h01⟩, h.h10⟩, h.h11⟩, fun h => ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩⟩
  rw [hset]
  exact (((hball'.preimage (hc 0 0)).inter (hball.preimage (hc 0 1))).inter
    (hball.preimage (hc 1 0))).inter (hball'.preimage (hc 1 1))

theorem congr_subset_localIntegralSet (n : ℕ) :
    (congr K v n : Set G) ⊆ AutomorphicForm.localIntegralSet K v := by
  intro g hg
  rw [AutomorphicForm.mem_localIntegralSet]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact (mem_congr.mp hg).integral i j
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact (mem_congr.mp ((congr K v n).inv_mem hg)).integral i j

theorem isCompact_congr (n : ℕ) : IsCompact (congr K v n : Set G) :=
  (AutomorphicForm.isCompact_localIntegralSet K v).of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ (isOpen_congr n)) (congr_subset_localIntegralSet n)

theorem eq_one_of_forall_mem_congr {g : G} (hg : ∀ n, g ∈ congr K v n) : g = 1 := by
  have h00 : (g : Mat) 0 0 - 1 = 0 := eq_zero_of_forall_v_le _ fun n => (hg n).h00
  have h01 : (g : Mat) 0 1 = 0 := eq_zero_of_forall_v_le _ fun n => (hg n).h01
  have h10 : (g : Mat) 1 0 = 0 := eq_zero_of_forall_v_le _ fun n => (hg n).h10
  have h11 : (g : Mat) 1 1 - 1 = 0 := eq_zero_of_forall_v_le _ fun n => (hg n).h11
  apply gl_eq_of_entries
  · simpa [sub_eq_zero] using h00
  · simpa using h01
  · simpa using h10
  · simpa [sub_eq_zero] using h11

theorem exists_congr_subset {U : Set G} (hU : IsOpen U) (h1 : (1 : G) ∈ U) :
    ∃ n, (congr K v n : Set G) ⊆ U := by
  have hdir : Directed (fun x1 x2 : Set G => x1 ⊇ x2) fun n : ℕ => (congr K v n : Set G) := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · exact fun g hg => congr_antitone' (le_max_left i j) hg
    · exact fun g hg => congr_antitone' (le_max_right i j) hg
  refine exists_subset_nhds_of_isCompact' hdir (fun n => isCompact_congr n)
    (fun n => Subgroup.isClosed_of_isOpen _ (isOpen_congr n)) ?_
  intro x hx
  rw [Set.mem_iInter] at hx
  have : x = 1 := eq_one_of_forall_mem_congr hx
  subst this
  exact hU.mem_nhds h1

theorem exists_finset_cosets (n : ℕ) :
    ∃ T : Finset G, (∀ t ∈ T, t ∈ AutomorphicForm.localIntegralSet K v) ∧
      ∀ k ∈ AutomorphicForm.localIntegralSet K v, ∃ t ∈ T, t⁻¹ * k ∈ congr K v n := by
  classical
  let ι := AutomorphicForm.localIntegralSet K v
  obtain ⟨S, hS⟩ := (AutomorphicForm.isCompact_localIntegralSet K v).elim_finite_subcover
    (fun t : ι => (t : G) • (congr K v n : Set G)) (fun t => (isOpen_congr n).leftCoset _)
    (by
      intro k hk
      rw [Set.mem_iUnion]
      exact ⟨⟨k, hk⟩, by rw [mem_leftCoset_iff, inv_mul_cancel]; exact (congr K v n).one_mem⟩)
  refine ⟨S.image (fun t : ι => (t : G)), ?_, ?_⟩
  · intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨t', _, rfl⟩ := ht
    exact t'.2
  · intro k hk
    have := hS hk
    rw [Set.mem_iUnion₂] at this
    obtain ⟨t, htS, hkt⟩ := this
    refine ⟨(t : G), Finset.mem_image_of_mem _ htS, ?_⟩
    rwa [mem_leftCoset_iff] at hkt

theorem entries_mul_le {M N : Mat} {α β : ℤᵐ⁰} (hM : ∀ i j, Valued.v (M i j) ≤ α)
    (hN : ∀ i j, Valued.v (N i j) ≤ β) (i j : Fin 2) : Valued.v ((M * N) i j) ≤ α * β := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine v_add_le ?_ ?_ <;> rw [Valuation.map_mul] <;> exact mul_le_mul' (hM _ _) (hN _ _)

theorem isCong_iff_entries {n : ℕ} (m : Mat) :
    IsCong n m ↔ ∀ i j, Valued.v ((m - 1) i j) ≤ lvl n := by
  constructor
  · intro h i j
    fin_cases i <;> fin_cases j
    · simpa using h.h00
    · simpa using h.h01
    · simpa using h.h10
    · simpa using h.h11
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using h 0 0
    · simpa using h 0 1
    · simpa using h 1 0
    · simpa using h 1 1

theorem conj_mem_congr {n : ℕ} {s : G} (hs : s ∈ AutomorphicForm.localIntegralSet K v) {g : G}
    (hg : g ∈ congr K v n) : s⁻¹ * g * s ∈ congr K v n := by
  rw [AutomorphicForm.mem_localIntegralSet] at hs
  rw [mem_congr, isCong_iff_entries] at hg ⊢
  have hmat : ((s⁻¹ * g * s : G) : Mat) - 1 = ((s⁻¹ : G) : Mat) * ((g : Mat) - 1) * (s : Mat) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← Matrix.GeneralLinearGroup.coe_mul,
      ← Matrix.GeneralLinearGroup.coe_mul, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one]
  intro i j
  rw [hmat]
  have h1 : ∀ i j, Valued.v ((((s⁻¹ : G) : Mat) * ((g : Mat) - 1)) i j) ≤ 1 * lvl n :=
    entries_mul_le (fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hs.2 i j)) hg
  have := entries_mul_le h1
    (fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hs.1 i j)) i j
  simpa using this

theorem mem_localIntegralSet_of_mem_localLevelOne_top {k : G}
    (hk : k ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤) : k ∈ AutomorphicForm.localIntegralSet K v := by
  rw [AdelicDock.mem_localLevelOne_iff] at hk
  exact ⟨hk.1.integral, hk.2.integral⟩

theorem isLocalLevelOne_top_of_integral {m : Mat}
    (h : ∀ i j, m i j ∈ v.adicCompletionIntegers K) : AdelicDock.IsLocalLevelOne (𝓞 K) K v ⊤ m := by
  refine ⟨h, ?_, ?_⟩
  · rw [AdelicLevel.idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 0)
  · rw [AdelicLevel.idealBound_top]
    exact v_sub_le ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 1)) (by simp)

theorem mem_localLevelOne_top_of_mem_localIntegralSet {k : G}
    (hk : k ∈ AutomorphicForm.localIntegralSet K v) : k ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤ := by
  rw [AdelicDock.mem_localLevelOne_iff]
  exact ⟨isLocalLevelOne_top_of_integral hk.1, isLocalLevelOne_top_of_integral hk.2⟩

theorem diagOne_mem_localLevelOne_top {t : Fˣ} (ht : Valued.v (t : F) = 1) :
    (AdelicLevel.diagOne t : G) ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤ := by
  have key : ∀ u : Fˣ, Valued.v (u : F) = 1 →
      ∀ i j, ((AdelicLevel.diagOne u : G) : Mat) i j ∈ v.adicCompletionIntegers K := by
    intro u hu i j
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, diagOne_coe]
    fin_cases i <;> fin_cases j <;> simp [hu]
  rw [AdelicDock.mem_localLevelOne_iff]
  refine ⟨isLocalLevelOne_top_of_integral (key t ht), ?_⟩
  rw [← map_inv]
  refine isLocalLevelOne_top_of_integral (key t⁻¹ ?_)
  rw [Units.val_inv_eq_inv_val, map_inv₀, ht, inv_one]

end GLtwo

section RightTranslation

variable {G : Type*} [Group G]

def rt (h : G) (W : G → ℂ) : G → ℂ := fun g => W (g * h)

@[scoped simp] theorem rt_apply (h : G) (W : G → ℂ) (g : G) : rt h W g = W (g * h) := rfl

theorem rt_one (W : G → ℂ) : rt 1 W = W := by
  funext g; simp

theorem rt_mul (g h : G) (W : G → ℂ) : rt (g * h) W = rt g (rt h W) := by
  funext x; simp [mul_assoc]

@[scoped simp] theorem rt_add (h : G) (W₁ W₂ : G → ℂ) : rt h (W₁ + W₂) = rt h W₁ + rt h W₂ := rfl
@[scoped simp] theorem rt_sub (h : G) (W₁ W₂ : G → ℂ) : rt h (W₁ - W₂) = rt h W₁ - rt h W₂ := rfl
@[scoped simp] theorem rt_smul (h : G) (c : ℂ) (W : G → ℂ) : rt h (c • W) = c • rt h W := rfl
@[scoped simp] theorem rt_zero (h : G) : rt h (0 : G → ℂ) = 0 := rfl

def rtL (h : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun := rt h
  map_add' := rt_add h
  map_smul' := rt_smul h

@[scoped simp] theorem rtL_apply (h : G) (W : G → ℂ) : rtL h W = rt h W := rfl

theorem rt_sum {ι : Type*} (s : Finset ι) (h : G) (f : ι → G → ℂ) :
    rt h (∑ i ∈ s, f i) = ∑ i ∈ s, rt h (f i) :=
  map_sum (rtL h) f s

end RightTranslation

section Core

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => HeightOneSpectrum.adicCompletion K v
local notation "𝒪" => HeightOneSpectrum.adicCompletionIntegers K v
local notation "Mat" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)
local notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)
local notation "𝓀" => IsLocalRing.ResidueField (HeightOneSpectrum.adicCompletionIntegers K v)

structure WhittData (ψ : AddChar (HeightOneSpectrum.adicCompletion K v) ℂ)
    (V : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) → ℂ)) : Prop where
  stab : ∀ W ∈ V, ∀ h : G, rt h W ∈ V
  law : ∀ W ∈ V, ∀ (x : F) (g : G), W (UnramifiedWhittaker.unipotent x * g) = ψ x * W g
  adm : ∀ U : Subgroup G, IsOpen (U : Set G) → ∃ B : Finset (G → ℂ), ∀ W ∈ V,
    (∀ k ∈ U, ∀ g : G, W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (G → ℂ))
  triv : ∀ x : F, Valued.v x ≤ 1 → ψ x = 1

variable (K v) in

def fixedSp (V : Submodule ℂ (G → ℂ)) (n : ℕ) : Submodule ℂ (G → ℂ) where
  carrier := {u | u ∈ V ∧ ∀ k ∈ congr K v n, rt k u = u}
  zero_mem' := ⟨V.zero_mem, fun k _ => rfl⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨V.add_mem ha hb, fun k hk => by rw [rt_add, ha' k hk, hb' k hk]⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    exact ⟨V.smul_mem c ha, fun k hk => by rw [rt_smul, ha' k hk]⟩

theorem mem_fixedSp {V : Submodule ℂ (G → ℂ)} {n : ℕ} {u : G → ℂ} :
    u ∈ fixedSp K v V n ↔ u ∈ V ∧ ∀ k ∈ congr K v n, rt k u = u := Iff.rfl

theorem finite_fixedSp {ψ : AddChar F ℂ} {V : Submodule ℂ (G → ℂ)} (hV : WhittData ψ V) (n : ℕ) :
    Module.Finite ℂ (fixedSp K v V n) := by
  obtain ⟨B, hB⟩ := hV.adm (congr K v n) (isOpen_congr n)
  haveI := FiniteDimensional.span_finset ℂ B
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (B : Set (G → ℂ))) ?_
  intro u hu
  exact hB u hu.1 fun k hk g => by have := congrFun (hu.2 k hk) g; simpa using this

def unif (ϖ : F) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) : Fˣ := Units.mk0 ϖ (uniformizer_ne_zero hϖ)

@[scoped simp] theorem unif_coe (ϖ : F) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) : (unif ϖ hϖ : F) = ϖ := rfl

def aElt (ϖ : F) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) : G := AdelicLevel.diagOne (unif ϖ hϖ)

theorem aElt_coe (ϖ : F) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) :
    ((aElt ϖ hϖ : G) : Mat) = !![ϖ, 0; 0, 1] := by
  rw [aElt, diagOne_coe, unif_coe]

theorem aElt_inv_coe (ϖ : F) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) :
    (((aElt ϖ hϖ)⁻¹ : G) : Mat) = !![ϖ⁻¹, 0; 0, 1] := by
  rw [aElt, ← map_inv, diagOne_coe, Units.val_inv_eq_inv_val, unif_coe]

theorem conj_aElt_mem_congr {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {n : ℕ} {g : G}
    (h00 : Valued.v ((g : Mat) 0 0 - 1) ≤ lvl n) (h01 : Valued.v ((g : Mat) 0 1) ≤ lvl (n + 1))
    (h10 : Valued.v ((g : Mat) 1 0) ≤ lvl n) (h11 : Valued.v ((g : Mat) 1 1 - 1) ≤ lvl n) :
    (aElt ϖ hϖ)⁻¹ * g * aElt ϖ hϖ ∈ congr K v n := by
  have hϖ0 := uniformizer_ne_zero hϖ
  have hent : ∀ i j, (((aElt ϖ hϖ)⁻¹ * g * aElt ϖ hϖ : G) : Mat) i j =
      ((((aElt ϖ hϖ)⁻¹ : G) : Mat) i 0 * (g : Mat) 0 0 + (((aElt ϖ hϖ)⁻¹ : G) : Mat) i 1 * (g : Mat) 1 0) *
        ((aElt ϖ hϖ : G) : Mat) 0 j +
      ((((aElt ϖ hϖ)⁻¹ : G) : Mat) i 0 * (g : Mat) 0 1 + (((aElt ϖ hϖ)⁻¹ : G) : Mat) i 1 * (g : Mat) 1 1) *
        ((aElt ϖ hϖ : G) : Mat) 1 j := by
    intro i j; rw [mul_coe_apply, mul_coe_apply, mul_coe_apply]
  have e00 : (((aElt ϖ hϖ)⁻¹ * g * aElt ϖ hϖ : G) : Mat) 0 0 = (g : Mat) 0 0 := by
    rw [hent, aElt_inv_coe, aElt_coe]; simp; field_simp
  have e01 : (((aElt ϖ hϖ)⁻¹ * g * aElt ϖ hϖ : G) : Mat) 0 1 = ϖ⁻¹ * (g : Mat) 0 1 := by
    rw [hent, aElt_inv_coe, aElt_coe]; simp
  have e10 : (((aElt ϖ hϖ)⁻¹ * g * aElt ϖ hϖ : G) : Mat) 1 0 = (g : Mat) 1 0 * ϖ := by
    rw [hent, aElt_inv_coe, aElt_coe]; simp
  have e11 : (((aElt ϖ hϖ)⁻¹ * g * aElt ϖ hϖ : G) : Mat) 1 1 = (g : Mat) 1 1 := by
    rw [hent, aElt_inv_coe, aElt_coe]; simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e00]; exact h00
  · rw [e01, Valuation.map_mul, map_inv₀, hϖ]
    calc (WithZero.exp (-1 : ℤ))⁻¹ * Valued.v ((g : Mat) 0 1) ≤ (WithZero.exp (-1 : ℤ))⁻¹ * lvl (n + 1) :=
          mul_le_mul_right h01 _
      _ = lvl n := by
          rw [lvl, lvl, ← WithZero.exp_neg, ← WithZero.exp_add, WithZero.exp_inj]; push_cast; ring
  · rw [e10]
    calc Valued.v ((g : Mat) 1 0 * ϖ) = Valued.v ((g : Mat) 1 0) * Valued.v ϖ := Valuation.map_mul _ _ _
      _ ≤ lvl n * 1 := mul_le_mul' h10 (by rw [hϖ]; exact (exp_neg_succ_le_one 0))
      _ = lvl n := mul_one _
  · rw [e11]; exact h11

variable {ψ : AddChar (HeightOneSpectrum.adicCompletion K v) ℂ}
  {V : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) → ℂ)}

theorem rt_aElt_fixed {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {n : ℕ} {u : G → ℂ}
    (hu : u ∈ fixedSp K v V n) {g : G} (hg : (aElt ϖ hϖ)⁻¹ * g * aElt ϖ hϖ ∈ congr K v n) :
    rt g (rt (aElt ϖ hϖ) u) = rt (aElt ϖ hϖ) u := by
  have : g * aElt ϖ hϖ = aElt ϖ hϖ * ((aElt ϖ hϖ)⁻¹ * g * aElt ϖ hϖ) := by group
  rw [← rt_mul, this, rt_mul, hu.2 _ hg]

theorem rt_unipotent_small {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {n : ℕ} {u : G → ℂ}
    (hu : u ∈ fixedSp K v V n) {w : F} (hw : Valued.v w ≤ lvl (n + 1)) :
    rt (UnramifiedWhittaker.unipotent w) (rt (aElt ϖ hϖ) u) = rt (aElt ϖ hϖ) u := by
  refine rt_aElt_fixed hϖ hu (conj_aElt_mem_congr hϖ ?_ ?_ ?_ ?_) <;>
    simp [unipotent_coe, hw]

theorem rt_unipotent_congr {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {n : ℕ} {u : G → ℂ}
    (hu : u ∈ fixedSp K v V n) {w w' : F} (hw : Valued.v (w - w') ≤ lvl (n + 1)) :
    rt (UnramifiedWhittaker.unipotent w) (rt (aElt ϖ hϖ) u) =
      rt (UnramifiedWhittaker.unipotent w') (rt (aElt ϖ hϖ) u) := by
  have : (UnramifiedWhittaker.unipotent w : G) =
      UnramifiedWhittaker.unipotent w' * UnramifiedWhittaker.unipotent (w - w') := by
    rw [unipotent_mul]; congr 1; ring
  rw [this, rt_mul, rt_unipotent_small hϖ hu hw]

theorem rt_diag_fixed {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {n : ℕ} {u : G → ℂ}
    (hu : u ∈ fixedSp K v V n) {t₁ t₂ : F} (h₁ : Valued.v (t₁ - 1) ≤ lvl n)
    (h₂ : Valued.v (t₂ - 1) ≤ lvl n) (h : t₁ * t₂ - 0 * 0 ≠ 0) :
    rt (gl2 t₁ 0 0 t₂ h) (rt (aElt ϖ hϖ) u) = rt (aElt ϖ hϖ) u := by
  refine rt_aElt_fixed hϖ hu (conj_aElt_mem_congr hϖ ?_ ?_ ?_ ?_) <;> simp [h₁, h₂]

theorem rt_lowerk_fixed {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {n : ℕ} {u : G → ℂ}
    (hu : u ∈ fixedSp K v V n) {c w w' : F} (hc : Valued.v c ≤ lvl n) (hw : Valued.v w ≤ 1)
    (hw' : Valued.v w' ≤ 1) (h : (1 - w' * c) * (1 + c * w) - 0 * c ≠ 0) :
    rt (gl2 (1 - w' * c) 0 c (1 + c * w) h) (rt (aElt ϖ hϖ) u) = rt (aElt ϖ hϖ) u := by
  refine rt_aElt_fixed hϖ hu (conj_aElt_mem_congr hϖ ?_ ?_ ?_ ?_)
  · simp only [gl2_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]
    have : 1 - w' * c - 1 = -(w' * c) := by ring
    rw [this, Valuation.map_neg]
    exact v_mul_le_lvl_right hw' hc
  · simp
  · simpa using hc
  · simp only [gl2_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have : 1 + c * w - 1 = c * w := by ring
    rw [this]
    exact v_mul_le_lvl_left hc hw

local instance instFintypeResidueField : Fintype 𝓀 := Fintype.ofFinite _

def resLift (r : 𝓀) : 𝒪 := (IsLocalRing.residue_surjective r).choose

theorem residue_resLift (r : 𝓀) : IsLocalRing.residue 𝒪 (resLift r) = r :=
  (IsLocalRing.residue_surjective r).choose_spec

theorem v_le_exp_neg_one_of_residue_eq {x y : 𝒪} (h : IsLocalRing.residue 𝒪 x = IsLocalRing.residue 𝒪 y) :
    Valued.v ((x : F) - (y : F)) ≤ WithZero.exp (-1 : ℤ) := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    AdelicHaar.mem_maximalIdeal_iff_valued_lt_one] at h
  rw [← v_lt_one_iff]
  simpa using h

def repU (ϖ : F) (n : ℕ) (r : 𝓀) : G := UnramifiedWhittaker.unipotent (ϖ ^ (n + 1) * (resLift r : F))

theorem v_rep_le {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (n : ℕ) (r : 𝓀) :
    Valued.v (ϖ ^ (n + 1) * (resLift r : F)) ≤ lvl n := by
  rw [Valuation.map_mul, v_uniformizer_pow hϖ, lvl]
  have : Valued.v (resLift r : F) ≤ 1 := (resLift r).2
  calc WithZero.exp (-((n + 1 : ℕ) : ℤ)) * Valued.v (resLift r : F) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) * 1 :=
        mul_le_mul_right this _
    _ = WithZero.exp (-((n : ℤ) + 1)) := by rw [mul_one]; push_cast; ring_nf

def Top (ϖ : F) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (n : ℕ) (u : G → ℂ) : G → ℂ :=
  ∑ r : 𝓀, rt (repU ϖ n r) (rt (aElt ϖ hϖ) u)

theorem Top_add (ϖ : F) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (n : ℕ) (u₁ u₂ : G → ℂ) :
    Top ϖ hϖ n (u₁ + u₂) = Top ϖ hϖ n u₁ + Top ϖ hϖ n u₂ := by
  simp only [Top, rt_add, Finset.sum_add_distrib]

theorem Top_smul (ϖ : F) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (n : ℕ) (c : ℂ) (u : G → ℂ) :
    Top ϖ hϖ n (c • u) = c • Top ϖ hϖ n u := by
  simp only [Top, rt_smul, Finset.smul_sum]

theorem Top_mem (hV : WhittData ψ V) (ϖ : F) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (n : ℕ)
    {u : G → ℂ} (hu : u ∈ V) : Top ϖ hϖ n u ∈ V :=
  V.sum_mem fun r _ => hV.stab _ (hV.stab _ hu _) _

theorem rt_unipotent_Top {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {n : ℕ} {u : G → ℂ}
    (hu : u ∈ fixedSp K v V n) {b : F} (hb : Valued.v b ≤ lvl n) :
    rt (UnramifiedWhittaker.unipotent b) (Top ϖ hϖ n u) = Top ϖ hϖ n u := by
  have hϖ0 := uniformizer_ne_zero hϖ
  have hpow : (ϖ ^ (n + 1) : F) ≠ 0 := pow_ne_zero _ hϖ0

  have hb' : Valued.v (b / ϖ ^ (n + 1)) ≤ 1 := by
    rw [map_div₀, v_uniformizer_pow hϖ, div_le_iff₀ (by simp), one_mul]
    simpa [lvl] using hb
  obtain ⟨b', hb'F⟩ : ∃ b' : 𝒪, (b' : F) = b / ϖ ^ (n + 1) :=
    ⟨⟨b / ϖ ^ (n + 1), (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hb'⟩, rfl⟩
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : 𝓀, IsLocalRing.residue 𝒪 b' = s₀ := ⟨_, rfl⟩
  rw [Top, rt_sum]
  have hterm : ∀ r : 𝓀, rt (UnramifiedWhittaker.unipotent b) (rt (repU ϖ n r) (rt (aElt ϖ hϖ) u)) =
      rt (repU ϖ n (r + s₀)) (rt (aElt ϖ hϖ) u) := by
    intro r
    rw [← rt_mul, repU, unipotent_mul, repU]
    apply rt_unipotent_congr hϖ hu
    obtain ⟨z, hz⟩ : ∃ z : 𝒪, z = b' + resLift r - resLift (r + s₀) := ⟨_, rfl⟩
    have hzF : (z : F) = (b' : F) + (resLift r : F) - (resLift (r + s₀) : F) := by
      rw [hz]; push_cast; ring
    have : b + ϖ ^ (n + 1) * (resLift r : F) - ϖ ^ (n + 1) * (resLift (r + s₀) : F) =
        ϖ ^ (n + 1) * (z : F) := by
      rw [hzF, hb'F]
      field_simp
    rw [this, Valuation.map_mul, v_uniformizer_pow hϖ, lvl]
    have hres : Valued.v (z : F) ≤ WithZero.exp (-1 : ℤ) := by
      have hzr : IsLocalRing.residue 𝒪 z = 0 := by
        rw [hz, map_sub, map_add, residue_resLift, residue_resLift, hs₀, add_comm, sub_self]
      rw [IsLocalRing.residue_eq_zero_iff, AdelicHaar.mem_maximalIdeal_iff_valued_lt_one] at hzr
      exact (v_lt_one_iff _).mp hzr
    calc WithZero.exp (-((n + 1 : ℕ) : ℤ)) * Valued.v (z : F)
        ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) * WithZero.exp (-1 : ℤ) := mul_le_mul_right hres _
      _ = WithZero.exp (-(((n + 1 : ℕ) : ℤ) + 1)) := by rw [← WithZero.exp_add, neg_add]
  simp_rw [hterm]
  exact Equiv.sum_comp (Equiv.addRight s₀) (fun r => rt (repU ϖ n r) (rt (aElt ϖ hϖ) u))

theorem rt_diag_Top {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {n : ℕ} {u : G → ℂ}
    (hu : u ∈ fixedSp K v V n) {t₁ t₂ : F} (h₁ : Valued.v (t₁ - 1) ≤ lvl n)
    (h₂ : Valued.v (t₂ - 1) ≤ lvl n) (h : t₁ * t₂ - 0 * 0 ≠ 0) :
    rt (gl2 t₁ 0 0 t₂ h) (Top ϖ hϖ n u) = Top ϖ hϖ n u := by
  have hvt₂ : Valued.v t₂ = 1 := v_eq_one_of_sub_one h₂
  have ht₂ : t₂ ≠ 0 := ne_zero_of_v_eq_one hvt₂
  rw [Top, rt_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← rt_mul, repU, diag_mul_unipotent, rt_mul, rt_diag_fixed hϖ hu h₁ h₂]
  apply rt_unipotent_congr hϖ hu
  have hvw := v_rep_le hϖ n r
  generalize ϖ ^ (n + 1) * (resLift r : F) = w at hvw ⊢
  have : t₁ * w * t₂⁻¹ - w = w * (((t₁ - 1) - (t₂ - 1)) * t₂⁻¹) := by field_simp; ring
  rw [this, Valuation.map_mul, Valuation.map_mul, map_inv₀, hvt₂, inv_one, mul_one]
  calc Valued.v w * Valued.v (t₁ - 1 - (t₂ - 1)) ≤ lvl n * lvl n :=
        mul_le_mul' hvw (v_sub_le h₁ h₂)
    _ ≤ lvl (n + 1) := by
        rw [lvl, lvl, ← WithZero.exp_add, WithZero.exp_le_exp]; push_cast; omega

theorem rt_lower_Top {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {n : ℕ} {u : G → ℂ}
    (hu : u ∈ fixedSp K v V n) {c : F} (hc : Valued.v c ≤ lvl n) (hL : (1 : F) * 1 - 0 * c ≠ 0) :
    rt (gl2 1 0 c 1 hL) (Top ϖ hϖ n u) = Top ϖ hϖ n u := by
  rw [Top, rt_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← rt_mul, repU]
  have hvw := v_rep_le hϖ n r
  generalize ϖ ^ (n + 1) * (resLift r : F) = w at hvw ⊢
  have hcw1 : Valued.v (1 + c * w) = 1 := by
    apply v_eq_one_of_sub_one (n := n)
    have : 1 + c * w - 1 = c * w := by ring
    rw [this]; exact v_mul_le_lvl_left hc (hvw.trans (lvl_le_one n))
  have hcw : 1 + c * w ≠ 0 := ne_zero_of_v_eq_one hcw1
  have hcw' : 1 + w * c ≠ 0 := by rwa [mul_comm w c]
  have hw' : Valued.v (w / (1 + c * w)) ≤ 1 := by
    rw [map_div₀, hcw1, div_one]; exact hvw.trans (lvl_le_one n)
  have hk : (1 - w / (1 + c * w) * c) * (1 + c * w) - 0 * c ≠ 0 := by
    have : (1 - w / (1 + c * w) * c) * (1 + c * w) - 0 * c = 1 := by field_simp; ring
    rw [this]; exact one_ne_zero
  rw [lower_mul_unipotent c w hcw hL hk, rt_mul,
    rt_lowerk_fixed hϖ hu hc (hvw.trans (lvl_le_one n)) hw' hk]
  apply rt_unipotent_congr hϖ hu
  have : w / (1 + c * w) - w = -(c * (w * w) / (1 + c * w)) := by field_simp; ring
  rw [this, Valuation.map_neg, map_div₀, hcw1, div_one, Valuation.map_mul, Valuation.map_mul]
  calc Valued.v c * (Valued.v w * Valued.v w) ≤ lvl n * (lvl n * 1) :=
        mul_le_mul' hc (mul_le_mul' hvw (hvw.trans (lvl_le_one n)))
    _ ≤ lvl (n + 1) := by
        rw [mul_one, lvl, lvl, ← WithZero.exp_add, WithZero.exp_le_exp]; push_cast; omega

theorem Top_mem_fixedSp (hV : WhittData ψ V) {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {n : ℕ}
    {u : G → ℂ} (hu : u ∈ fixedSp K v V n) : Top ϖ hϖ n u ∈ fixedSp K v V n := by
  refine ⟨Top_mem hV ϖ hϖ n hu.1, fun k hk => ?_⟩
  have hk' := mem_congr.mp hk
  have hα : (k : Mat) 0 0 ≠ 0 := ne_zero_of_v_eq_one hk'.v00
  obtain ⟨hL, hD, hfac⟩ := iwahori_factor k hα
  have hvα : Valued.v ((k : Mat) 0 0) = 1 := hk'.v00

  have hc : Valued.v ((k : Mat) 1 0 / (k : Mat) 0 0) ≤ lvl n := by
    rw [map_div₀, hvα, div_one]; exact hk'.h10
  have hb : Valued.v ((k : Mat) 0 1 / (k : Mat) 0 0) ≤ lvl n := by
    rw [map_div₀, hvα, div_one]; exact hk'.h01
  have hd : Valued.v ((k : Mat) 1 1 - (k : Mat) 0 1 * (k : Mat) 1 0 / (k : Mat) 0 0 - 1) ≤ lvl n := by
    have : (k : Mat) 1 1 - (k : Mat) 0 1 * (k : Mat) 1 0 / (k : Mat) 0 0 - 1 =
        ((k : Mat) 1 1 - 1) - (k : Mat) 0 1 * ((k : Mat) 1 0 / (k : Mat) 0 0) := by ring
    rw [this]
    exact v_sub_le hk'.h11 (v_mul_le_lvl_left hk'.h01 (hc.trans (lvl_le_one n)))
  rw [hfac, rt_mul, rt_mul, rt_unipotent_Top hϖ hu hb, rt_diag_Top hϖ hu hk'.h00 hd, rt_lower_Top hϖ hu hc]

def TopL (hV : WhittData ψ V) (ϖ : F) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (n : ℕ) :
    fixedSp K v V n →ₗ[ℂ] fixedSp K v V n where
  toFun u := ⟨Top ϖ hϖ n u, Top_mem_fixedSp hV hϖ u.2⟩
  map_add' u₁ u₂ := by ext1; simp [Top_add]
  map_smul' c u := by ext1; simp [Top_smul]

@[scoped simp] theorem TopL_apply_coe (hV : WhittData ψ V) (ϖ : F) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (n : ℕ)
    (u : fixedSp K v V n) : ((TopL hV ϖ hϖ n u : fixedSp K v V n) : G → ℂ) = Top ϖ hϖ n u := rfl

variable (K v) in

def Nsp : Submodule ℂ (G → ℂ) where
  carrier := {f | ∃ m : ℤ, ∀ y : Fˣ, Valued.v (y : F) ≤ WithZero.exp m → f (AdelicLevel.diagOne y) = 0}
  zero_mem' := ⟨0, fun _ _ => rfl⟩
  add_mem' := by
    rintro f g ⟨m₁, h₁⟩ ⟨m₂, h₂⟩
    refine ⟨min m₁ m₂, fun y hy => ?_⟩
    rw [Pi.add_apply, h₁ y (hy.trans (WithZero.exp_le_exp.mpr (min_le_left _ _))),
      h₂ y (hy.trans (WithZero.exp_le_exp.mpr (min_le_right _ _))), add_zero]
  smul_mem' := by
    rintro c f ⟨m, h⟩
    exact ⟨m, fun y hy => by rw [Pi.smul_apply, h y hy, smul_zero]⟩

theorem mem_Nsp {f : G → ℂ} :
    f ∈ Nsp K v ↔ ∃ m : ℤ, ∀ y : Fˣ, Valued.v (y : F) ≤ WithZero.exp m → f (AdelicLevel.diagOne y) = 0 :=
  Iff.rfl

theorem rt_aElt_mem_Nsp {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {f : G → ℂ} (hf : f ∈ Nsp K v) :
    rt (aElt ϖ hϖ) f ∈ Nsp K v := by
  obtain ⟨m, hm⟩ := hf
  refine ⟨m, fun y hy => ?_⟩
  rw [rt_apply, aElt, ← map_mul]
  apply hm
  rw [Units.val_mul, unif_coe, Valuation.map_mul, hϖ]
  calc Valued.v (y : F) * WithZero.exp (-1 : ℤ) ≤ WithZero.exp m * 1 :=
        mul_le_mul' hy (exp_neg_succ_le_one 0)
    _ = WithZero.exp m := mul_one _

theorem rt_unipotent_sub_mem_Nsp (hV : WhittData ψ V) {f : G → ℂ} (hf : f ∈ V) (w : F) :
    rt (UnramifiedWhittaker.unipotent w) f - f ∈ Nsp K v := by
  refine ⟨-WithZero.log (Valued.v w), fun y hy => ?_⟩
  rw [Pi.sub_apply, rt_apply, diagOne_mul_unipotent, hV.law f hf, sub_eq_zero]
  suffices h : ψ ((y : F) * w) = 1 by rw [h, one_mul]
  apply hV.triv
  rw [Valuation.map_mul]
  by_cases hw : Valued.v w = 0
  · rw [hw, mul_zero]; exact zero_le'
  · calc Valued.v (y : F) * Valued.v w ≤ WithZero.exp (-WithZero.log (Valued.v w)) * Valued.v w :=
          mul_le_mul_left hy _
      _ = 1 := by
          conv_lhs => rw [← WithZero.exp_log hw]
          rw [← WithZero.exp_add, WithZero.log_exp, neg_add_cancel, WithZero.exp_zero]

theorem Top_sub_mem_Nsp (hV : WhittData ψ V) {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (n : ℕ)
    {u : G → ℂ} (hu : u ∈ V) :
    Top ϖ hϖ n u - (Fintype.card 𝓀 : ℂ) • rt (aElt ϖ hϖ) u ∈ Nsp K v := by
  have : Top ϖ hϖ n u - (Fintype.card 𝓀 : ℂ) • rt (aElt ϖ hϖ) u =
      ∑ r : 𝓀, (rt (repU ϖ n r) (rt (aElt ϖ hϖ) u) - rt (aElt ϖ hϖ) u) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, Top]
  rw [this]
  exact (Nsp K v).sum_mem fun r _ => rt_unipotent_sub_mem_Nsp hV (hV.stab _ hu _) _

theorem TopL_pow_sub_mem_Nsp (hV : WhittData ψ V) {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (n : ℕ)
    (u : fixedSp K v V n) (i : ℕ) :
    (((TopL hV ϖ hϖ n ^ i) u : fixedSp K v V n) : G → ℂ) -
      ((Fintype.card 𝓀 : ℂ) ^ i) • rt (aElt ϖ hϖ ^ i) (u : G → ℂ) ∈ Nsp K v := by
  induction i with
  | zero => simp [rt_one]
  | succ i ih =>
    set y : fixedSp K v V n := (TopL hV ϖ hϖ n ^ i) u with hy
    have h1 : Top ϖ hϖ n (y : G → ℂ) - (Fintype.card 𝓀 : ℂ) • rt (aElt ϖ hϖ) (y : G → ℂ) ∈ Nsp K v :=
      Top_sub_mem_Nsp hV hϖ n y.2.1
    have h2 : (Fintype.card 𝓀 : ℂ) • rt (aElt ϖ hϖ) ((y : G → ℂ) -
        ((Fintype.card 𝓀 : ℂ) ^ i) • rt (aElt ϖ hϖ ^ i) (u : G → ℂ)) ∈ Nsp K v :=
      (Nsp K v).smul_mem _ (rt_aElt_mem_Nsp hϖ ih)
    have heq : (((TopL hV ϖ hϖ n ^ (i + 1)) u : fixedSp K v V n) : G → ℂ) -
        ((Fintype.card 𝓀 : ℂ) ^ (i + 1)) • rt (aElt ϖ hϖ ^ (i + 1)) (u : G → ℂ) =
        (Top ϖ hϖ n (y : G → ℂ) - (Fintype.card 𝓀 : ℂ) • rt (aElt ϖ hϖ) (y : G → ℂ)) +
        (Fintype.card 𝓀 : ℂ) • rt (aElt ϖ hϖ) ((y : G → ℂ) -
          ((Fintype.card 𝓀 : ℂ) ^ i) • rt (aElt ϖ hϖ ^ i) (u : G → ℂ)) := by
      rw [pow_succ', Module.End.mul_apply, ← hy, TopL_apply_coe, rt_sub, rt_smul, ← rt_mul, ← pow_succ',
        smul_sub, smul_smul, ← pow_succ']
      abel
    rw [heq]
    exact (Nsp K v).add_mem h1 h2

theorem key_recursion (hV : WhittData ψ V) {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (n : ℕ) :
    ∃ (d : ℕ) (c : ℕ → ℂ), ∀ u ∈ fixedSp K v V n, ∃ m : ℤ, ∀ y : Fˣ, Valued.v (y : F) ≤ WithZero.exp m →
      u (AdelicLevel.diagOne (y * unif ϖ hϖ ^ d)) =
        ∑ i ∈ Finset.range d, c i * u (AdelicLevel.diagOne (y * unif ϖ hϖ ^ i)) := by
  haveI := finite_fixedSp hV n
  obtain ⟨P, hP, hPT⟩ := LinearMap.exists_monic_and_aeval_eq_zero ℂ (TopL hV ϖ hϖ n)
  set q : ℂ := (Fintype.card 𝓀 : ℂ) with hq
  have hq0 : q ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  set d := P.natDegree with hd
  refine ⟨d, fun i => -(P.coeff i * q ^ i) / q ^ d, fun u hu => ?_⟩

  have hsum : ∑ i ∈ Finset.range (d + 1), P.coeff i • ((q ^ i) • rt (aElt ϖ hϖ ^ i) u) ∈ Nsp K v := by
    have h0 : ∑ i ∈ Finset.range (d + 1),
        P.coeff i • ((((TopL hV ϖ hϖ n ^ i) ⟨u, hu⟩ : fixedSp K v V n) : G → ℂ)) = 0 := by
      have := congrArg (fun f : fixedSp K v V n →ₗ[ℂ] fixedSp K v V n => ((f ⟨u, hu⟩ : fixedSp K v V n) : G → ℂ)) hPT
      simp only [Polynomial.aeval_eq_sum_range, LinearMap.zero_apply, ZeroMemClass.coe_zero,
        LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, Submodule.coe_sum,
        Submodule.coe_smul] at this
      exact this
    have : ∑ i ∈ Finset.range (d + 1), P.coeff i • ((q ^ i) • rt (aElt ϖ hϖ ^ i) u) =
        ∑ i ∈ Finset.range (d + 1), P.coeff i • ((q ^ i) • rt (aElt ϖ hϖ ^ i) u -
          (((TopL hV ϖ hϖ n ^ i) ⟨u, hu⟩ : fixedSp K v V n) : G → ℂ)) +
        ∑ i ∈ Finset.range (d + 1), P.coeff i • ((((TopL hV ϖ hϖ n ^ i) ⟨u, hu⟩ : fixedSp K v V n) : G → ℂ)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_sub, sub_add_cancel]
    rw [this, h0, add_zero]
    refine (Nsp K v).sum_mem fun i _ => (Nsp K v).smul_mem _ ?_
    have := (Nsp K v).neg_mem (TopL_pow_sub_mem_Nsp hV hϖ n ⟨u, hu⟩ i)
    rwa [neg_sub] at this
  obtain ⟨m, hm⟩ := hsum
  refine ⟨m, fun y hy => ?_⟩
  have h := hm y hy
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rt_apply] at h
  rw [Finset.sum_range_succ, hP.coeff_natDegree, one_mul] at h
  have hqd : q ^ d ≠ 0 := pow_ne_zero _ hq0
  have key : u (AdelicLevel.diagOne y * aElt ϖ hϖ ^ d) =
      ∑ i ∈ Finset.range d, -(P.coeff i * q ^ i) / q ^ d * u (AdelicLevel.diagOne y * aElt ϖ hϖ ^ i) := by
    have hS : ∑ i ∈ Finset.range d, -(P.coeff i * q ^ i) / q ^ d * u (AdelicLevel.diagOne y * aElt ϖ hϖ ^ i) =
        (-(q ^ d)⁻¹) * ∑ i ∈ Finset.range d, P.coeff i * (q ^ i * u (AdelicLevel.diagOne y * aElt ϖ hϖ ^ i)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    rw [hS]
    generalize (∑ i ∈ Finset.range d, P.coeff i * (q ^ i * u (AdelicLevel.diagOne y * aElt ϖ hϖ ^ i))) = S at h ⊢
    field_simp
    linear_combination h
  simpa only [aElt, ← map_pow, ← map_mul] using key

theorem vanish_large (hV : WhittData ψ V) (hnt : ∃ x₀ : F, ψ x₀ ≠ 1) (n : ℕ) :
    ∃ m₀ : ℤ, ∀ u ∈ fixedSp K v V n, ∀ y : Fˣ, WithZero.exp m₀ ≤ Valued.v (y : F) →
      u (AdelicLevel.diagOne y) = 0 := by
  obtain ⟨x₀, hx₀⟩ := hnt
  have hx₀0 : Valued.v x₀ ≠ 0 := by
    intro h
    rw [Valuation.zero_iff] at h
    rw [h, AddChar.map_zero_eq_one] at hx₀
    exact hx₀ rfl
  set L₀ := WithZero.log (Valued.v x₀) with hL₀
  refine ⟨L₀ + ((n : ℤ) + 1), fun u hu y hy => ?_⟩
  have hy0 : Valued.v (y : F) ≠ 0 := by rw [ne_eq, Valuation.zero_iff]; exact y.ne_zero
  set x : F := (y : F)⁻¹ * x₀ with hx
  have hvx : Valued.v x ≤ lvl n := by
    rw [hx, Valuation.map_mul, map_inv₀, ← WithZero.exp_log hx₀0, ← hL₀]
    have hy' : (Valued.v (y : F))⁻¹ ≤ (WithZero.exp (L₀ + ((n : ℤ) + 1)))⁻¹ := inv_anti₀ WithZero.exp_pos hy
    calc (Valued.v (y : F))⁻¹ * WithZero.exp L₀ ≤ (WithZero.exp (L₀ + ((n : ℤ) + 1)))⁻¹ * WithZero.exp L₀ :=
          mul_le_mul_left hy' _
      _ = lvl n := by
          rw [lvl, ← WithZero.exp_neg, ← WithZero.exp_add, WithZero.exp_inj]; ring
  have hmem : (UnramifiedWhittaker.unipotent x : G) ∈ congr K v n := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [unipotent_coe, hvx]
  have h1 := congrFun (hu.2 _ hmem) (AdelicLevel.diagOne y)
  rw [rt_apply, diagOne_mul_unipotent, hV.law u hu.1] at h1
  have hyx : (y : F) * x = x₀ := by rw [hx, ← mul_assoc, mul_inv_cancel₀ y.ne_zero, one_mul]
  rw [hyx] at h1
  have : (ψ x₀ - 1) * u (AdelicLevel.diagOne y) = 0 := by rw [sub_mul, one_mul, h1, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hx₀
  · exact h

end Core

section Recursion

theorem geometric_bound (d : ℕ) (c : ℕ → ℂ) (φ : ℤ → ℂ) (j₁ : ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hrec : ∀ j : ℤ, j₁ ≤ j → φ (j + d) = ∑ i ∈ Finset.range d, c i * φ (j + i))
    (hbase : ∀ j : ℤ, j < j₁ + d → ‖φ j‖ ≤ B) (j : ℤ) :
    ‖φ j‖ ≤ B * (max 1 (∑ i ∈ Finset.range d, ‖c i‖)) ^ (j - j₁).toNat := by
  set R := max 1 (∑ i ∈ Finset.range d, ‖c i‖) with hR
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR0 : 0 ≤ R := zero_le_one.trans hR1
  have hRc : ∑ i ∈ Finset.range d, ‖c i‖ ≤ R := le_max_right _ _
  suffices H : ∀ k : ℕ, ∀ j : ℤ, (j - j₁).toNat = k → ‖φ j‖ ≤ B * R ^ k from H _ j rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro j hj
    by_cases hjd : j < j₁ + d
    · calc ‖φ j‖ ≤ B := hbase j hjd
        _ ≤ B * R ^ k := le_mul_of_one_le_right hB (one_le_pow₀ hR1)
    · push Not at hjd
      have hj' : j₁ ≤ j - d := by omega
      have hjeq : j = (j - d) + d := by ring
      rw [hjeq, hrec _ hj']
      by_cases hd : d = 0
      · subst hd
        simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
        positivity
      have hk1 : 1 ≤ k := by omega
      calc ‖∑ i ∈ Finset.range d, c i * φ (j - d + i)‖
          ≤ ∑ i ∈ Finset.range d, ‖c i‖ * ‖φ (j - d + i)‖ :=
            norm_sum_le_of_le _ fun i _ => by rw [norm_mul]
        _ ≤ ∑ i ∈ Finset.range d, ‖c i‖ * (B * R ^ (k - 1)) := by
            refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            rw [Finset.mem_range] at hi
            have hlt : (j - d + i - j₁).toNat < k := by omega
            calc ‖φ (j - d + i)‖ ≤ B * R ^ (j - d + i - j₁).toNat := ih _ hlt _ rfl
              _ ≤ B * R ^ (k - 1) :=
                  mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR1 (by omega)) hB
        _ = (∑ i ∈ Finset.range d, ‖c i‖) * (B * R ^ (k - 1)) := by rw [Finset.sum_mul]
        _ ≤ R * (B * R ^ (k - 1)) := mul_le_mul_of_nonneg_right hRc (by positivity)
        _ = B * R ^ k := by
            conv_rhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
            ring

theorem exists_common_threshold {α : Type*} (T : Finset α) (P : α → ℤ → Prop)
    (hmono : ∀ a m m', m' ≤ m → P a m → P a m') (h : ∀ a ∈ T, ∃ m, P a m) : ∃ m, ∀ a ∈ T, P a m := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a T ha ih =>
    obtain ⟨m₁, hm₁⟩ := h a (Finset.mem_insert_self a T)
    obtain ⟨m₂, hm₂⟩ := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    refine ⟨min m₁ m₂, fun b hb => ?_⟩
    rw [Finset.mem_insert] at hb
    rcases hb with rfl | hb
    · exact hmono _ _ _ (min_le_left _ _) hm₁
    · exact hmono _ _ _ (min_le_right _ _) (hm₂ b hb)

theorem pow_toNat_le_max (R Q : ℝ) (hR : 1 ≤ R) (hQ : 1 ≤ Q) (M : ℕ) (hRM : R ≤ Q ^ M) (j j₁ : ℤ)
    (hj₁ : 0 ≤ j₁) : R ^ (j - j₁).toNat ≤ max 1 ((Q ^ (-j)) ^ M)⁻¹ := by
  by_cases hj : j₁ ≤ j
  · have hle : (j - j₁).toNat ≤ j.toNat := by omega
    have hQM : 1 ≤ Q ^ M := one_le_pow₀ hQ
    refine le_max_of_le_right ?_
    calc R ^ (j - j₁).toNat ≤ (Q ^ M) ^ (j - j₁).toNat := pow_le_pow_left₀ (zero_le_one.trans hR) hRM _
      _ ≤ (Q ^ M) ^ j.toNat := pow_le_pow_right₀ hQM hle
      _ = ((Q ^ (-j)) ^ M)⁻¹ := by
          have hjnat : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg (hj₁.trans hj)
          rw [← inv_pow, zpow_neg, inv_inv]
          conv_rhs => rw [← hjnat, zpow_natCast]
          rw [← pow_mul, ← pow_mul, mul_comm]
  · have : (j - j₁).toNat = 0 := by omega
    rw [this, pow_zero]
    exact le_max_left _ _

end Recursion

section Assembly

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => HeightOneSpectrum.adicCompletion K v
local notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)

variable {ψ : AddChar (HeightOneSpectrum.adicCompletion K v) ℂ}
  {V : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) → ℂ)}

def normBase (v : HeightOneSpectrum (𝓞 K)) : NNReal := (Ideal.absNorm v.asIdeal : NNReal)

theorem one_lt_normBase : 1 < (normBase v : ℝ) := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  rw [normBase]; exact_mod_cast this

theorem modulus_eq_zpow (y : F) (j : ℤ) (hy : Valued.v y = WithZero.exp (-j)) :
    (LanglandsTunnell.TateLocal.modulus y : ℝ) = (normBase v : ℝ) ^ (-j) := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v y, coe_nnnorm,
    NumberField.FinitePlace.norm_def, hy,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  rw [NNReal.coe_zpow, normBase]
  congr 1

theorem majorant (hV : WhittData ψ V) (hnt : ∃ x₀ : F, ψ x₀ ≠ 1) {W : G → ℂ} (hW : W ∈ V)
    (hsmW : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, W (g * k) = W g) :
    ∃ (C : ℝ) (M : ℕ) (c : ℝ), 0 ≤ C ∧ 0 < c ∧
      ∀ (y : Fˣ) (k : G), k ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤ →
        ‖W (AdelicLevel.diagOne y * k)‖ ≤ C * max 1 ((LanglandsTunnell.TateLocal.modulus (y : F)) ^ M)⁻¹ ∧
        (c < LanglandsTunnell.TateLocal.modulus (y : F) → W (AdelicLevel.diagOne y * k) = 0) := by
  classical
  obtain ⟨U, hUo, hUW⟩ := hsmW
  obtain ⟨n, hn⟩ := exists_congr_subset (K := K) (v := v) hUo U.one_mem
  have hWfix : W ∈ fixedSp K v V n := ⟨hW, fun k hk => funext fun g => hUW k (hn hk) g⟩
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer K v
  obtain ⟨d, cf, hrec⟩ := key_recursion hV hϖ n
  obtain ⟨T, hTint, hTcov⟩ := exists_finset_cosets (K := K) (v := v) n
  obtain ⟨m₀, hm₀⟩ := vanish_large hV hnt n

  have hus : ∀ s ∈ T, rt s W ∈ fixedSp K v V n := fun s hs =>
    ⟨hV.stab W hW s, fun k hk => by
      rw [← rt_mul, show k * s = s * (s⁻¹ * k * s) by group, rt_mul,
        hWfix.2 _ (conj_mem_congr (hTint s hs) hk)]⟩

  obtain ⟨m, hm⟩ := exists_common_threshold T
    (fun s m => ∀ y : Fˣ, Valued.v (y : F) ≤ WithZero.exp m →
      rt s W (AdelicLevel.diagOne (y * unif ϖ hϖ ^ d)) =
        ∑ i ∈ Finset.range d, cf i * rt s W (AdelicLevel.diagOne (y * unif ϖ hϖ ^ i)))
    (fun s m m' hmm' h y hy => h y (hy.trans (WithZero.exp_le_exp.mpr hmm')))
    (fun s hs => hrec _ (hus s hs))

  set φ : G → ℤ → ℂ := fun s j => rt s W (AdelicLevel.diagOne (unif ϖ hϖ ^ j)) with hφ
  have hvϖj : ∀ j : ℤ, Valued.v ((unif ϖ hϖ ^ j : Fˣ) : F) = WithZero.exp (-j) := by
    intro j; rw [Units.val_zpow_eq_zpow_val, unif_coe, v_uniformizer_zpow hϖ]
  have hφrec : ∀ s ∈ T, ∀ j : ℤ, -m ≤ j → φ s (j + d) = ∑ i ∈ Finset.range d, cf i * φ s (j + i) := by
    intro s hs j hj
    have := hm s hs (unif ϖ hϖ ^ j) (by rw [hvϖj, WithZero.exp_le_exp]; omega)
    simp only [hφ, ← zpow_natCast, ← zpow_add] at this ⊢
    exact this
  have hφvan : ∀ s ∈ T, ∀ j : ℤ, j ≤ -m₀ → φ s j = 0 := by
    intro s hs j hj
    exact hm₀ _ (hus s hs) _ (by rw [hvϖj, WithZero.exp_le_exp]; omega)

  set j₁ : ℤ := max 0 (-m) with hj₁
  set Bs : G → ℝ := fun s => ∑ j ∈ Finset.Ioo (-m₀) (j₁ + d), ‖φ s j‖ with hBs
  have hBs0 : ∀ s, 0 ≤ Bs s := fun s => Finset.sum_nonneg fun j _ => norm_nonneg _
  have hbase : ∀ s ∈ T, ∀ j : ℤ, j < j₁ + d → ‖φ s j‖ ≤ Bs s := by
    intro s hs j hj
    by_cases hj' : j ≤ -m₀
    · rw [hφvan s hs j hj', norm_zero]; exact hBs0 s
    · exact Finset.single_le_sum (f := fun j => ‖φ s j‖) (fun j _ => norm_nonneg _)
        (Finset.mem_Ioo.mpr ⟨by omega, hj⟩)
  set R : ℝ := max 1 (∑ i ∈ Finset.range d, ‖cf i‖) with hR
  have hR1 : 1 ≤ R := le_max_left _ _
  have hgeom : ∀ s ∈ T, ∀ j : ℤ, ‖φ s j‖ ≤ Bs s * R ^ (j - j₁).toNat := fun s hs j =>
    geometric_bound d cf (φ s) j₁ (Bs s) (hBs0 s) (fun j hj => hφrec s hs j (by omega)) (hbase s hs) j
  set B : ℝ := ∑ s ∈ T, Bs s with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun s _ => hBs0 s
  have hBsB : ∀ s ∈ T, Bs s ≤ B := fun s hs => Finset.single_le_sum (fun s _ => hBs0 s) hs

  have hQ1 : 1 < (normBase v : ℝ) := one_lt_normBase
  obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt R hQ1
  refine ⟨B, M, (normBase v : ℝ) ^ m₀, hB0, zpow_pos (zero_lt_one.trans hQ1) _, fun y k hk => ?_⟩

  obtain ⟨j, t, ht, hyt, hvy⟩ := exists_eq_zpow_mul ϖ hϖ (y : F) y.ne_zero
  set tu : Fˣ := Units.mk0 t (ne_zero_of_v_eq_one ht) with htu
  have hyu : y = unif ϖ hϖ ^ j * tu := by
    ext; rw [Units.val_mul, Units.val_zpow_eq_zpow_val, unif_coe, htu, Units.val_mk0, hyt]
  have hk' : AdelicLevel.diagOne tu * k ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤ :=
    mul_mem (diagOne_mem_localLevelOne_top (by rw [htu, Units.val_mk0]; exact ht)) hk
  obtain ⟨s, hs, hsk⟩ := hTcov _ (mem_localIntegralSet_of_mem_localLevelOne_top hk')
  have hval : W (AdelicLevel.diagOne y * k) = φ s j := by
    have hrt : rt (AdelicLevel.diagOne tu * k) W = rt s W := by
      rw [show AdelicLevel.diagOne tu * k = s * (s⁻¹ * (AdelicLevel.diagOne tu * k)) by group, rt_mul,
        hWfix.2 _ hsk]
    have := congrFun hrt (AdelicLevel.diagOne (unif ϖ hϖ ^ j))
    rw [rt_apply, rt_apply] at this
    rw [hyu, map_mul, mul_assoc, this]
    rfl
  have hmod : (LanglandsTunnell.TateLocal.modulus (y : F) : ℝ) = (normBase v : ℝ) ^ (-j) :=
    modulus_eq_zpow (y : F) j hvy
  refine ⟨?_, ?_⟩
  · rw [hval]
    calc ‖φ s j‖ ≤ Bs s * R ^ (j - j₁).toNat := hgeom s hs j
      _ ≤ B * max 1 (((normBase v : ℝ) ^ (-j)) ^ M)⁻¹ :=
          mul_le_mul (hBsB s hs) (pow_toNat_le_max R _ hR1 hQ1.le M hM.le j j₁ (le_max_left _ _))
            (by positivity) hB0
      _ = B * ((max 1 ((LanglandsTunnell.TateLocal.modulus (y : F)) ^ M)⁻¹ : NNReal) : ℝ) := by
          rw [NNReal.coe_max, NNReal.coe_one, NNReal.coe_inv, NNReal.coe_pow, hmod]
  · intro hc
    rw [hval]
    apply hφvan s hs
    rw [hmod, zpow_lt_zpow_iff_right₀ hQ1] at hc
    omega

end Assembly

end KirillovBound
p2m_reactivate "P2MW.S_AutomorphicForm_WhittakerModel_exists_norm_diagOne_mul_le_of_irreducible_admissible.KirillovBound"

end
p2m_reactivate "P2MW.S_AutomorphicForm_WhittakerModel_exists_norm_diagOne_mul_le_of_irreducible_admissible.KirillovBound"

open IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal NumberField.AdelicLevel

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (V : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))
    (hstab : ∀ W ∈ V, ∀ h : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * h)) ∈ V)
    (hlaw : ∀ W ∈ V, ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      W (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * W g)
    (hsm : ∀ W ∈ V, ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g)
    (hadm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), ∀ W ∈ V, (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) →
        W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hirr : ∀ W₀ ∈ V, W₀ ≠ 0 → ∀ W ∈ V,
      W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h)))
    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hcen : ∀ W ∈ V, ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      W (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω z : ℂˣ) : ℂ) * W g) :
    ∀ W ∈ V, ∃ (C : ℝ) (M : ℕ) (c : ℝ), 0 ≤ C ∧ 0 < c ∧
      ∀ (y : (p.adicCompletion ℚ)ˣ) (k : GL (Fin 2) (p.adicCompletion ℚ)), k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
        ‖W (diagOne y * k)‖ ≤ C * max 1 ((modulus (y : p.adicCompletion ℚ)) ^ M)⁻¹ ∧
        (c < modulus (y : p.adicCompletion ℚ) → W (diagOne y * k) = 0) := by
  intro W hW
  have hV : KirillovBound.WhittData (NumberField.StandardAddChar.psiLocal ℚ p) V :=
    { stab := fun W hW h => hstab W hW h
      law := hlaw
      adm := hadm
      triv := fun x hx => by
        rw [NumberField.StandardAddChar.psiLocal_rat_eq_psiV]
        exact NumberField.StandardAddChar.psiV_eq_one_of_mem_integers p
          ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hx) }
  have hnt : ∃ x₀ : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x₀ ≠ 1 :=
    ⟨_, by
      rw [NumberField.StandardAddChar.psiLocal_rat_eq_psiV]
      exact NumberField.StandardAddChar.psiV_algebraMap_inv_ne_one p⟩
  exact KirillovBound.majorant hV hnt hW (hsm W hW)

end S_AutomorphicForm_WhittakerModel_exists_norm_diagOne_mul_le_of_irreducible_admissible
end P2MW
export P2MW.S_AutomorphicForm_WhittakerModel_exists_norm_diagOne_mul_le_of_irreducible_admissible (solution)
