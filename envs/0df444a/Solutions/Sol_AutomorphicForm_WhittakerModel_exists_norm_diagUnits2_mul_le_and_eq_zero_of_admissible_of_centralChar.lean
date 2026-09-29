-- Prove2me | solution 1 for AutomorphicForm.WhittakerModel.exists_norm_diagUnits2_mul_le_and_eq_zero_of_admissible_of_centralChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/9bc8f71b-31ac-5405-bc34-27a9034f9ece

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_forall_diagZ_mul_eq_zero_and_norm_le_mul_zpow_of_admissible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_WhittakerModel_exists_norm_diagUnits2_mul_le_and_eq_zero_of_admissible_of_centralChar

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

noncomputable section

section KBblock
open IsDedekindDomain NumberField
open scoped WithZero Pointwise

namespace KBKD

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

end GLtwo

end KBKD
p2m_reactivate "P2MW.S_AutomorphicForm_WhittakerModel_exists_norm_diagUnits2_mul_le_and_eq_zero_of_admissible_of_centralChar.KBKD"

end KBblock
p2m_reactivate "P2MW.S_AutomorphicForm_WhittakerModel_exists_norm_diagUnits2_mul_le_and_eq_zero_of_admissible_of_centralChar.KBKD"

namespace SSKD

section Generic

variable {G : Type*} [Group G]

theorem translate_mem_span (f : G → ℂ) (h : G) {W : G → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h'))) :
    (fun g : G => W (g * h)) ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h')) := by
  induction hW using Submodule.span_induction with
  | mem W hWm =>
      obtain ⟨h', rfl⟩ := hWm
      exact Submodule.subset_span ⟨h * h', funext fun g => by simp only [mul_assoc]⟩
  | zero => exact Submodule.zero_mem _
  | add W₁ W₂ _ _ h₁ h₂ =>
      have : (fun g : G => (W₁ + W₂) (g * h)) = (fun g : G => W₁ (g * h)) + fun g : G => W₂ (g * h) := rfl
      rw [this]; exact Submodule.add_mem _ h₁ h₂
  | smul a W _ h₁ =>
      have : (fun g : G => (a • W) (g * h)) = a • fun g : G => W (g * h) := rfl
      rw [this]; exact Submodule.smul_mem _ a h₁

theorem span_le_span_of_mem (f W₀ : G → ℂ)
    (h₀ : f ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => W₀ (g * h'))) :
    Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h')) ≤
      Submodule.span ℂ (Set.range fun h' : G => fun g : G => W₀ (g * h')) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨h, rfl⟩
  exact translate_mem_span W₀ h h₀

theorem law_of_mem_span (f : G → ℂ) (a : G) (χ : ℂ) (hf : ∀ g : G, f (a * g) = χ * f g) {W : G → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h'))) :
    ∀ g : G, W (a * g) = χ * W g := by
  induction hW using Submodule.span_induction with
  | mem W hWm =>
      obtain ⟨h', rfl⟩ := hWm
      intro g
      show f (a * g * h') = χ * f (g * h')
      rw [mul_assoc, hf]
  | zero => intro g; simp
  | add W₁ W₂ _ _ h₁ h₂ => intro g; simp only [Pi.add_apply, h₁ g, h₂ g]; ring
  | smul c W _ h₁ => intro g; simp only [Pi.smul_apply, smul_eq_mul, h₁ g]; ring

variable [TopologicalSpace G] [ContinuousMul G]

theorem exists_open_stabilizer_of_mem_span (f : G → ℂ) (K : Subgroup G) (hK : IsOpen (K : Set G))
    (hf : ∀ k ∈ K, ∀ g : G, f (g * k) = f g) {W : G → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h'))) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, W (g * k) = W g := by
  induction hW using Submodule.span_induction with
  | mem W hWm =>
      obtain ⟨h, rfl⟩ := hWm
      refine ⟨K.comap (MulAut.conj h⁻¹).toMonoidHom, ?_, ?_⟩
      · have hc : Continuous fun k : G => h⁻¹ * k * h⁻¹⁻¹ :=
          (continuous_const.mul continuous_id).mul continuous_const
        have hset : ((K.comap (MulAut.conj h⁻¹).toMonoidHom : Subgroup G) : Set G) =
            (fun k : G => h⁻¹ * k * h⁻¹⁻¹) ⁻¹' (K : Set G) := by
          ext k
          simp only [Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
            SetLike.mem_coe]
        rw [hset]
        exact hK.preimage hc
      · intro k hk g
        rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hk
        show f (g * k * h) = f (g * h)
        rw [show g * k * h = g * h * (h⁻¹ * k * h) by simp only [mul_assoc, mul_inv_cancel_left]]
        exact hf _ hk (g * h)
  | zero => exact ⟨⊤, by simp, fun _ _ _ => rfl⟩
  | add W₁ W₂ _ _ h₁ h₂ =>
      obtain ⟨U₁, hU₁, hW₁⟩ := h₁
      obtain ⟨U₂, hU₂, hW₂⟩ := h₂
      refine ⟨U₁ ⊓ U₂, ?_, ?_⟩
      · rw [Subgroup.coe_inf]; exact hU₁.inter hU₂
      · intro k hk g
        rw [Subgroup.mem_inf] at hk
        simp only [Pi.add_apply, hW₁ k hk.1 g, hW₂ k hk.2 g]
  | smul c W _ h₁ =>
      obtain ⟨U, hU, hWU⟩ := h₁
      exact ⟨U, hU, fun k hk g => by simp only [Pi.smul_apply, hWU k hk g]⟩

end Generic
p2m_reactivate "P2MW.S_AutomorphicForm_WhittakerModel_exists_norm_diagUnits2_mul_le_and_eq_zero_of_admissible_of_centralChar.KBKD"

end SSKD
p2m_reactivate "P2MW.S_AutomorphicForm_WhittakerModel_exists_norm_diagUnits2_mul_le_and_eq_zero_of_admissible_of_centralChar.KBKD"

namespace WBGauge

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)

theorem scalar2_coe (u : (F)ˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : G2) : Matrix (Fin 2) (Fin 2) F) = !![(u : F), 0; 0, (u : F)] := by
  show Matrix.scalar (Fin 2) (u : F) = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar]

theorem diagUnits2_eq_scalar_mul (a₁ a₂ : (F)ˣ) :
    (diagUnits2 a₁ a₂ : G2) = Matrix.GeneralLinearGroup.scalar (Fin 2) a₂ * diagUnits2 (a₁ * a₂⁻¹) 1 := by
  apply Units.ext
  rw [Units.val_mul, coe_diagUnits2, coe_diagUnits2, scalar2_coe, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one]
  have h : (a₂ : F) ≠ 0 := a₂.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem diagUnits2_mul_one (x y : (F)ˣ) :
    (diagUnits2 (x * y) 1 : G2) = diagUnits2 x 1 * diagUnits2 y 1 := by
  apply Units.ext
  rw [Units.val_mul, coe_diagUnits2, coe_diagUnits2, coe_diagUnits2, Units.val_mul, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagUnits2_zpow_eq_diagZ (π : (F)ˣ) (m : ℤ) :
    (diagUnits2 (π ^ m) 1 : G2) = diagZ (π : F) π.ne_zero m := by
  apply Units.ext
  rw [coe_diagUnits2, Units.val_zpow_eq_zpow_val, Units.val_one]
  rfl

theorem scalar_mul_comm (z : (F)ˣ) (g : G2) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) z = Matrix.GeneralLinearGroup.scalar (Fin 2) z * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, scalar2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem diagUnits2_unit_inv (u : (F)ˣ) : ((diagUnits2 u 1 : G2)⁻¹ : G2) = diagUnits2 u⁻¹ 1 := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← diagUnits2_mul_one, inv_mul_cancel]
  apply Units.ext
  rw [coe_diagUnits2, Units.val_one, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem diagUnits2_unit_mem (u : (F)ˣ) (hu : Valued.v (u : F) = 1) :
    (diagUnits2 u 1 : G2) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  have key : ∀ w : (F)ˣ, Valued.v (w : F) = 1 →
      AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ ((diagUnits2 w 1 : G2) : Matrix (Fin 2) (Fin 2) F) := by
    intro w hw
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, coe_diagUnits2]
      fin_cases i <;> fin_cases j <;> simp [hw]
    · rw [NumberField.AdelicLevel.idealBound_top, coe_diagUnits2]; simp
    · rw [NumberField.AdelicLevel.idealBound_top, coe_diagUnits2]; simp
  rw [AdelicDock.mem_localLevelOne_iff, diagUnits2_unit_inv]
  refine ⟨key u hu, key u⁻¹ ?_⟩
  rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]

theorem exists_eq_zpow_mul_unit (π : (F)ˣ) (hπ : Valued.v (π : F) = WithZero.exp (-1 : ℤ)) (y : (F)ˣ) :
    ∃ (m : ℤ) (u : (F)ˣ), Valued.v (u : F) = 1 ∧ y = π ^ m * u := by
  have hvy : Valued.v (y : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  set m : ℤ := -WithZero.log (Valued.v (y : F)) with hm
  have hvπm : Valued.v (((π ^ m : (F)ˣ)) : F) = Valued.v (y : F) := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, hm, neg_neg,
      WithZero.exp_log hvy]
  refine ⟨m, (π ^ m)⁻¹ * y, ?_, (mul_inv_cancel_left (π ^ m) y).symm⟩
  rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hvπm, inv_mul_cancel₀ hvy]

theorem v_zpow_mul_unit (π : (F)ˣ) (hπ : Valued.v (π : F) = WithZero.exp (-1 : ℤ)) (m : ℤ) (u : (F)ˣ)
    (hu : Valued.v (u : F) = 1) : Valued.v (((π ^ m * u : (F)ˣ)) : F) = WithZero.exp (-m) := by
  rw [Units.val_mul, map_mul, hu, mul_one, Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul,
    mul_neg, mul_one]

def qR : ℝ := ((Ideal.absNorm p.asIdeal : NNReal) : ℝ)

theorem one_lt_qR : 1 < qR p := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p
  unfold qR; exact_mod_cast this

theorem norm_eq_qR_zpow (y : F) (j : ℤ) (hy : Valued.v y = WithZero.exp (-j)) : ‖y‖ = qR p ^ (-j) := by
  rw [NumberField.FinitePlace.norm_def, hy, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, NNReal.coe_zpow]
  unfold qR
  congr 1

theorem norm_eq_one_of_v (u : F) (hu : Valued.v u = 1) : ‖u‖ = 1 := by
  have := norm_eq_qR_zpow p u 0 (by rw [hu, neg_zero, WithZero.exp_zero])
  rw [this, neg_zero, zpow_zero]

theorem isCompact_units_sphere : IsCompact {u : (F)ˣ | Valued.v (u : F) = 1} := by
  have hO : IsCompact ((p.adicCompletionIntegers ℚ : Set F)) := by
    rw [← LanglandsTunnell.TateLocal.coe_integersPositiveCompacts]
    exact (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ p).isCompact
  have hS : IsCompact {x : F | Valued.v x = 1} := by
    refine hO.of_isClosed_subset ?_ (fun x hx => by
      rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]; exact le_of_eq hx)
    have ho : IsOpen {x : F | Valued.v x = 1}ᶜ := by
      rw [isOpen_iff_mem_nhds]
      intro x hx
      rw [Set.mem_compl_iff, Set.mem_setOf_eq] at hx
      by_cases hx0 : (Valued.v x : WithZero (Multiplicative ℤ)) = 0
      · have h0 : x = 0 := (Valuation.zero_iff _).1 hx0
        subst h0
        have hball : {y : F | Valued.v y ≤ WithZero.exp (-1 : ℤ)} ∈ nhds (0 : F) :=
          (KBKD.isOpen_ball (K := ℚ) (v := p) (-1)).mem_nhds (by simp)
        refine Filter.mem_of_superset hball fun y hy => ?_
        rw [Set.mem_compl_iff, Set.mem_setOf_eq]
        intro h1
        rw [Set.mem_setOf_eq, h1, ← WithZero.exp_zero, WithZero.exp_le_exp] at hy
        omega
      · have h := Valued.locally_const hx0
        refine Filter.mem_of_superset h fun y hy => ?_
        rw [Set.mem_compl_iff, Set.mem_setOf_eq]
        rw [Set.mem_setOf_eq] at hy
        rw [hy]; exact hx
    exact ⟨ho⟩
  have himage : (Units.val : (F)ˣ → F) '' {u : (F)ˣ | Valued.v (u : F) = 1} = {x : F | Valued.v x = 1} := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · intro hx
      have hx0 : x ≠ 0 := by intro h; rw [h, Valuation.map_zero] at hx; exact zero_ne_one hx
      exact ⟨Units.mk0 x hx0, hx, rfl⟩
  rw [(Units.isEmbedding_val₀ (G₀ := F)).isCompact_iff, himage]
  exact hS

def prinUnits (n : ℕ) : Subgroup (F)ˣ where
  carrier := {u | Valued.v ((u : F) - 1) ≤ KBKD.lvl n}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have hva : Valued.v (a : F) = 1 := KBKD.v_eq_one_of_sub_one ha
    have e : ((a * b : (F)ˣ) : F) - 1 = (a : F) * ((b : F) - 1) + ((a : F) - 1) := by rw [Units.val_mul]; ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ha)
    rw [Valuation.map_mul, hva, one_mul]; exact hb
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [Units.val_inv_eq_inv_val]
    exact KBKD.v_inv_sub_one ha

theorem isOpen_prinUnits (n : ℕ) : IsOpen (prinUnits p n : Set (F)ˣ) := by
  have hset : (prinUnits p n : Set (F)ˣ) = (fun u : (F)ˣ => (u : F) - 1) ⁻¹' {x | Valued.v x ≤ KBKD.lvl n} := rfl
  rw [hset]
  exact (KBKD.isOpen_ball (K := ℚ) (v := p) _).preimage (Units.continuous_val.sub continuous_const)

theorem continuous_of_open_stabilizer' {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (f : G → ℂ) (hF : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, f (g * k) = f g) :
    Continuous f := by
  obtain ⟨U, hU, hinv⟩ := hF
  refine continuous_def.2 fun s _ => ?_
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun k => g * k) '' (U : Set G), ?_, ?_, ⟨1, U.one_mem, mul_one g⟩⟩
  · rintro _ ⟨k, hk, rfl⟩
    show f (g * k) ∈ s
    rw [hinv k hk g]; exact hg
  · exact (Homeomorph.mulLeft g).isOpenMap _ hU

theorem norm_char_unit_eq_one (θ : (F)ˣ →* ℂˣ) (n : ℕ)
    (hθ : ∀ z : (F)ˣ, Valued.v ((z : F) - 1) ≤ KBKD.lvl n → θ z = 1)
    (u : (F)ˣ) (hu : Valued.v (u : F) = 1) : ‖((θ u : ℂˣ) : ℂ)‖ = 1 := by

  have hcont : Continuous fun t : (F)ˣ => ((θ t : ℂˣ) : ℂ) := by
    refine continuous_of_open_stabilizer' _ ⟨prinUnits p n, isOpen_prinUnits p n, fun k hk g => ?_⟩
    rw [map_mul, hθ k hk, mul_one]

  obtain ⟨M, hM⟩ := (isCompact_units_sphere p).exists_bound_of_continuousOn hcont.continuousOn

  have hpow : ∀ (w : (F)ˣ), Valued.v (w : F) = 1 → ∀ k : ℕ, ‖((θ w : ℂˣ) : ℂ)‖ ^ k ≤ M := by
    intro w hw k
    have hmem : w ^ k ∈ {u : (F)ˣ | Valued.v (u : F) = 1} := by
      show Valued.v (((w ^ k : (F)ˣ)) : F) = 1
      rw [Units.val_pow_eq_pow_val, map_pow, hw, one_pow]
    have := hM _ hmem
    rwa [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
  have hle : ∀ (w : (F)ˣ), Valued.v (w : F) = 1 → ‖((θ w : ℂˣ) : ℂ)‖ ≤ 1 := by
    intro w hw
    by_contra h
    push Not at h
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt M h
    exact absurd (hpow w hw k) (not_le.2 hk)
  have h1 := hle u hu
  have h2 := hle u⁻¹ (by rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one])
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  have hpos : 0 < ‖((θ u : ℂˣ) : ℂ)‖ := norm_pos_iff.2 (θ u).ne_zero
  have h3 : 1 ≤ ‖((θ u : ℂˣ) : ℂ)‖ := by rwa [inv_le_one₀ hpos] at h2
  exact le_antisymm h1 h3

theorem norm_char_zpow_mul_unit (θ : (F)ˣ →* ℂˣ) (n : ℕ)
    (hθ : ∀ z : (F)ˣ, Valued.v ((z : F) - 1) ≤ KBKD.lvl n → θ z = 1)
    (π : (F)ˣ) (m : ℤ) (u : (F)ˣ) (hu : Valued.v (u : F) = 1) :
    ‖((θ (π ^ m * u) : ℂˣ) : ℂ)‖ = ‖((θ π : ℂˣ) : ℂ)‖ ^ m := by
  rw [map_mul, map_zpow, Units.val_mul, norm_mul, Units.val_zpow_eq_zpow_val, norm_zpow,
    norm_char_unit_eq_one p θ n hθ u hu, mul_one]

theorem zpow_eq_rpow (c : ℝ) (hc : 0 < c) (m : ℤ) :
    c ^ m = (qR p ^ (-m)) ^ (-Real.log c / Real.log (qR p)) := by
  have hq : 1 < qR p := one_lt_qR p
  have hq0 : 0 < qR p := zero_lt_one.trans hq
  have hlogq : Real.log (qR p) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hq0 hq.ne'
  rw [← Real.rpow_intCast (qR p) (-m), ← Real.rpow_mul hq0.le, Real.rpow_def_of_pos hq0,
    ← Real.rpow_intCast c m, Real.rpow_def_of_pos hc]
  congr 1
  field_simp
  push_cast
  ring

theorem exists_bound (C R : ℝ) (hC : 0 ≤ C) (hR : 0 < R) (N₁ : ℤ) :
    ∃ (C' : ℝ) (A : ℕ), 0 ≤ C' ∧ ∀ m : ℤ, N₁ ≤ m →
      C * R ^ m ≤ C' * max 1 (((qR p ^ (-m)) ^ A)⁻¹) := by
  have hq : 1 < qR p := one_lt_qR p
  have hq0 : 0 < qR p := zero_lt_one.trans hq
  obtain ⟨A, hA⟩ := pow_unbounded_of_one_lt (max R 1) hq
  refine ⟨C * max 1 (R ^ N₁), A, mul_nonneg hC (le_trans zero_le_one (le_max_left _ _)), fun m hm => ?_⟩
  have hRm : 0 < R ^ m := zpow_pos hR m
  have hmax1 : 1 ≤ max 1 (R ^ N₁) := le_max_left _ _
  have hmax2 : 1 ≤ max 1 (((qR p ^ (-m)) ^ A)⁻¹) := le_max_left _ _

  have key : R ^ m ≤ max 1 (R ^ N₁) * max 1 (((qR p ^ (-m)) ^ A)⁻¹) := by
    by_cases hm0 : 0 ≤ m
    ·
      have h1 : R ^ m ≤ (max R 1) ^ m := by
        rw [← Int.toNat_of_nonneg hm0, zpow_natCast, zpow_natCast]
        exact pow_le_pow_left₀ hR.le (le_max_left _ _) _
      have h2 : (max R 1) ^ m ≤ (qR p ^ A) ^ m := by
        rw [← Int.toNat_of_nonneg hm0, zpow_natCast, zpow_natCast]
        exact pow_le_pow_left₀ (le_trans zero_le_one (le_max_right _ _)) hA.le _
      have h3 : (qR p ^ A) ^ m = ((qR p ^ (-m)) ^ A)⁻¹ := by
        rw [← zpow_natCast (qR p ^ (-m)) A, ← zpow_mul, neg_mul, zpow_neg, inv_inv, ← zpow_natCast (qR p) A,
          ← zpow_mul, mul_comm]
      calc R ^ m ≤ (qR p ^ A) ^ m := h1.trans h2
        _ = ((qR p ^ (-m)) ^ A)⁻¹ := h3
        _ ≤ max 1 (((qR p ^ (-m)) ^ A)⁻¹) := le_max_right _ _
        _ ≤ max 1 (R ^ N₁) * max 1 (((qR p ^ (-m)) ^ A)⁻¹) := le_mul_of_one_le_left (le_trans zero_le_one hmax2) hmax1
    · push Not at hm0
      have h1 : R ^ m ≤ max 1 (R ^ N₁) := by
        by_cases hR1 : R ≤ 1
        ·
          have : R ^ m = R ^ N₁ * R ^ ((m - N₁).toNat : ℕ) := by
            rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), ← zpow_add₀ hR.ne']; congr 1; ring
          rw [this]
          calc R ^ N₁ * R ^ ((m - N₁).toNat : ℕ) ≤ R ^ N₁ * 1 :=
                mul_le_mul_of_nonneg_left (pow_le_one₀ hR.le hR1) (zpow_pos hR N₁).le
            _ = R ^ N₁ := mul_one _
            _ ≤ max 1 (R ^ N₁) := le_max_right _ _
        · push Not at hR1

          have : R ^ m = (R ^ ((-m).toNat : ℕ))⁻¹ := by
            rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), zpow_neg, inv_inv]
          rw [this]
          exact le_trans (inv_le_one_of_one_le₀ (one_le_pow₀ hR1.le)) (le_max_left _ _)
      calc R ^ m ≤ max 1 (R ^ N₁) := h1
        _ ≤ max 1 (R ^ N₁) * max 1 (((qR p ^ (-m)) ^ A)⁻¹) := le_mul_of_one_le_right (le_trans zero_le_one hmax1) hmax2
  calc C * R ^ m ≤ C * (max 1 (R ^ N₁) * max 1 (((qR p ^ (-m)) ^ A)⁻¹)) := mul_le_mul_of_nonneg_left key hC
    _ = C * max 1 (R ^ N₁) * max 1 (((qR p ^ (-m)) ^ A)⁻¹) := by ring

theorem main
    (θ : (F)ˣ →* ℂˣ)
    (w : G2 → ℂ)
    (hwlaw : ∀ (a : F) (g : G2), w (unipotent a * g) = NumberField.StandardAddChar.psiLocal ℚ p a * w g)
    (hwsm : ∃ U : Subgroup G2, IsOpen (U : Set G2) ∧ ∀ k ∈ U, ∀ g : G2, w (g * k) = w g)
    (hwadm : ∀ U : Subgroup G2, IsOpen (U : Set G2) →
      ∃ B : Finset (G2 → ℂ),
        ∀ w' ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w (g * h)),
          (∀ k ∈ U, ∀ g : G2, w' (g * k) = w' g) → w' ∈ Submodule.span ℂ (B : Set (G2 → ℂ)))
    (hcentral : ∀ (zc : (F)ˣ) (g : G2), w (Matrix.GeneralLinearGroup.scalar (Fin 2) zc * g) = ((θ zc : ℂˣ) : ℂ) * w g) :
    ∃ (C : ℝ) (A : ℕ) (τ : ℝ) (m₁ : ℤ), 0 ≤ C ∧
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ a₁ a₂ : (F)ˣ,
        ‖w (diagUnits2 a₁ a₂ * k)‖ ≤
            C * ‖(a₂ : F)‖ ^ τ * max 1 ((‖((a₁ * a₂⁻¹ : (F)ˣ) : F)‖ ^ A)⁻¹) ∧
        (WithZero.exp m₁ < Valued.v ((a₁ * a₂⁻¹ : (F)ˣ) : F) → w (diagUnits2 a₁ a₂ * k) = 0) := by
  classical
  by_cases hw0 : w = 0
  · refine ⟨0, 0, 0, 0, le_rfl, fun k hk a₁ a₂ => ⟨?_, fun _ => ?_⟩⟩
    · rw [hw0]; simp
    · rw [hw0]; rfl

  obtain ⟨U, hUo, hUw⟩ := hwsm
  have hwV : w ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w (g * h)) :=
    Submodule.subset_span ⟨1, funext fun g => by show w (g * 1) = w g; rw [mul_one]⟩
  have Vstab : ∀ W ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w (g * h)), ∀ h : G2,
      (fun g => W (g * h)) ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w (g * h)) :=
    fun W hW h => SSKD.translate_mem_span w h hW
  have Vlaw : ∀ W ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w (g * h)), ∀ (x : F) (g : G2),
      W (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * W g :=
    fun W hW x => SSKD.law_of_mem_span w (unipotent x) _ (hwlaw x) hW
  have Vsm : ∀ W ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w (g * h)),
      ∃ U' : Subgroup G2, IsOpen (U' : Set G2) ∧ ∀ k ∈ U', ∀ g : G2, W (g * k) = W g :=
    fun W hW => SSKD.exists_open_stabilizer_of_mem_span w U hUo hUw hW

  set ϖu : (F)ˣ := NumberField.AdelicLevel.uniformizerUnit ℚ p with hϖudef
  have hvϖ : Valued.v (ϖu : F) = WithZero.exp (-1 : ℤ) := NumberField.AdelicLevel.valued_uniformizerUnit ℚ p
  have hϖmem : (ϖu : F) ∈ p.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hvϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  set ϖi : p.adicCompletionIntegers ℚ := ⟨(ϖu : F), hϖmem⟩ with hϖidef
  have hπ : algebraMap (p.adicCompletionIntegers ℚ) F ϖi ≠ 0 := ϖu.ne_zero
  have hϖ' : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) F ϖi) = WithZero.exp (-1 : ℤ) := hvϖ

  obtain ⟨N₁, C, R, hC, hR, hmain⟩ :=
    AutomorphicForm.WhittakerModel.exists_forall_diagZ_mul_eq_zero_and_norm_le_mul_zpow_of_admissible p _
      Vstab Vlaw Vsm hwadm hπ hϖ' w hwV
  have hdiagZ : ∀ m : ℤ, diagZ (algebraMap (p.adicCompletionIntegers ℚ) F ϖi) hπ m = (diagUnits2 (ϖu ^ m) 1 : G2) := by
    intro m; rw [diagUnits2_zpow_eq_diagZ]; rfl

  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : G2, w g₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (funext h)
  obtain ⟨n, hn⟩ := KBKD.exists_congr_subset (K := ℚ) (v := p) hUo U.one_mem
  have hθ1 : ∀ z : (F)ˣ, Valued.v ((z : F) - 1) ≤ KBKD.lvl n → θ z = 1 := by
    intro z hz
    have hzc : (Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2) ∈ KBKD.congr ℚ p n := by
      show KBKD.IsCong n ((Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2) : Matrix (Fin 2) (Fin 2) F)
      rw [scalar2_coe]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hz]
    have h1 := hUw _ (hn hzc) g₀
    rw [scalar_mul_comm, hcentral] at h1
    exact Units.val_eq_one.1 ((mul_eq_right₀ hg₀).1 h1)

  set c : ℝ := ‖((θ ϖu : ℂˣ) : ℂ)‖ with hcdef
  have hc : 0 < c := norm_pos_iff.2 (θ ϖu).ne_zero
  set τ : ℝ := -Real.log c / Real.log (qR p) with hτdef
  obtain ⟨C', A, hC', hbound⟩ := exists_bound p C R hC hR N₁
  refine ⟨C', A, τ, -N₁, hC', fun k hk a₁ a₂ => ?_⟩

  obtain ⟨m, u, hu, hdec⟩ := exists_eq_zpow_mul_unit p ϖu hvϖ (a₁ * a₂⁻¹)
  have hk' : (diagUnits2 u 1 : G2) * k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ :=
    mul_mem (diagUnits2_unit_mem p u hu) hk
  have hval : w (diagUnits2 a₁ a₂ * k) =
      ((θ a₂ : ℂˣ) : ℂ) * w (diagZ (algebraMap (p.adicCompletionIntegers ℚ) F ϖi) hπ m * (diagUnits2 u 1 * k)) := by
    rw [diagUnits2_eq_scalar_mul, hdec, diagUnits2_mul_one, hdiagZ, mul_assoc, mul_assoc, hcentral]
  have hvt : Valued.v (((a₁ * a₂⁻¹ : (F)ˣ)) : F) = WithZero.exp (-m) := by rw [hdec]; exact v_zpow_mul_unit p ϖu hvϖ m u hu
  have hnt : ‖(((a₁ * a₂⁻¹ : (F)ˣ)) : F)‖ = qR p ^ (-m) := norm_eq_qR_zpow p _ m hvt
  obtain ⟨hvan, hle⟩ := hmain _ hk' m
  refine ⟨?_, fun hm₁ => ?_⟩
  ·
    obtain ⟨m₂, u₂, hu₂, hdec₂⟩ := exists_eq_zpow_mul_unit p ϖu hvϖ a₂
    have hθa₂ : ‖((θ a₂ : ℂˣ) : ℂ)‖ = ‖(a₂ : F)‖ ^ τ := by
      rw [hdec₂, norm_char_zpow_mul_unit p θ n hθ1 ϖu m₂ u₂ hu₂, norm_eq_qR_zpow p _ m₂ (v_zpow_mul_unit p ϖu hvϖ m₂ u₂ hu₂)]
      exact zpow_eq_rpow p c hc m₂
    rw [hval, norm_mul, hθa₂, hnt]
    by_cases hmN : m < N₁
    · rw [hvan hmN, norm_zero, mul_zero]
      exact mul_nonneg (mul_nonneg hC' (Real.rpow_nonneg (norm_nonneg _) _)) (le_trans zero_le_one (le_max_left _ _))
    · push Not at hmN
      calc ‖(a₂ : F)‖ ^ τ * ‖w (diagZ (algebraMap (p.adicCompletionIntegers ℚ) F ϖi) hπ m * (diagUnits2 u 1 * k))‖
          ≤ ‖(a₂ : F)‖ ^ τ * (C * R ^ m) := mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg (norm_nonneg _) _)
        _ ≤ ‖(a₂ : F)‖ ^ τ * (C' * max 1 (((qR p ^ (-m)) ^ A)⁻¹)) :=
            mul_le_mul_of_nonneg_left (hbound m hmN) (Real.rpow_nonneg (norm_nonneg _) _)
        _ = C' * ‖(a₂ : F)‖ ^ τ * max 1 (((qR p ^ (-m)) ^ A)⁻¹) := by ring
  ·
    rw [hvt, WithZero.exp_lt_exp] at hm₁
    rw [hval, hvan (by omega), mul_zero]

end WBGauge
p2m_reactivate "P2MW.S_AutomorphicForm_WhittakerModel_exists_norm_diagUnits2_mul_le_and_eq_zero_of_admissible_of_centralChar.KBKD"

end
p2m_reactivate "P2MW.S_AutomorphicForm_WhittakerModel_exists_norm_diagUnits2_mul_le_and_eq_zero_of_admissible_of_centralChar.KBKD"

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (a : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent a * g) = NumberField.StandardAddChar.psiLocal ℚ p a * w g)
    (hwsm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (hwadm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w' (g * k) = w' g) →
            w' ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (zc : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (Matrix.GeneralLinearGroup.scalar (Fin 2) zc * g) = ((θ zc : ℂˣ) : ℂ) * w g) :
    ∃ (C : ℝ) (A : ℕ) (τ : ℝ) (m₁ : ℤ), 0 ≤ C ∧
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ a₁ a₂ : (p.adicCompletion ℚ)ˣ,
        ‖w (diagUnits2 a₁ a₂ * k)‖ ≤
            C * ‖(a₂ : p.adicCompletion ℚ)‖ ^ τ *
              max 1 ((‖((a₁ * a₂⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)‖ ^ A)⁻¹) ∧
        (WithZero.exp m₁ < Valued.v ((a₁ * a₂⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) →
          w (diagUnits2 a₁ a₂ * k) = 0) :=
  WBGauge.main p θ w hwlaw hwsm hwadm hcentral

end S_AutomorphicForm_WhittakerModel_exists_norm_diagUnits2_mul_le_and_eq_zero_of_admissible_of_centralChar
end P2MW
export P2MW.S_AutomorphicForm_WhittakerModel_exists_norm_diagUnits2_mul_le_and_eq_zero_of_admissible_of_centralChar (solution)
