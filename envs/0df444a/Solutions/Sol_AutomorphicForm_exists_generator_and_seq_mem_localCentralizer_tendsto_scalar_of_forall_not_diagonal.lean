-- Prove2me | solution 1 for AutomorphicForm.exists_generator_and_seq_mem_localCentralizer_tendsto_scalar_of_forall_not_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/5cb2a4a6-ea37-552b-8a77-26acb849f837

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_generator_and_seq_mem_localCentralizer_tendsto_scalar_of_forall_not_diagonal

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

noncomputable section

namespace Ws31
namespace Torus

open AutomorphicForm Matrix

section Algebra

variable {F : Type*} [Field F]

def lin (γ : Matrix (Fin 2) (Fin 2) F) (x y : F) : Matrix (Fin 2) (Fin 2) F := x • (1 : Matrix (Fin 2) (Fin 2) F) + y • γ

theorem lin_apply (γ : Matrix (Fin 2) (Fin 2) F) (x y : F) (i j : Fin 2) :
    lin γ x y i j = x * (1 : Matrix (Fin 2) (Fin 2) F) i j + y * γ i j := by
  simp [lin, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem eta_fin_two (M : Matrix (Fin 2) (Fin 2) F) : M = !![M 0 0, M 0 1; M 1 0, M 1 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem lin_eq (γ : Matrix (Fin 2) (Fin 2) F) (x y : F) :
    lin γ x y = !![x + y * γ 0 0, y * γ 0 1; y * γ 1 0, x + y * γ 1 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [lin_apply]

theorem trace_lin (γ : Matrix (Fin 2) (Fin 2) F) (x y : F) :
    (lin γ x y).trace = 2 * x + γ.trace * y := by
  rw [lin_eq, Matrix.trace_fin_two_of, Matrix.trace_fin_two]; ring

theorem det_lin (γ : Matrix (Fin 2) (Fin 2) F) (x y : F) :
    (lin γ x y).det = x ^ 2 + γ.trace * x * y + γ.det * y ^ 2 := by
  rw [lin_eq, Matrix.det_fin_two_of, Matrix.trace_fin_two, Matrix.det_fin_two]; ring

theorem disc_lin (γ : Matrix (Fin 2) (Fin 2) F) (x y : F) :
    (lin γ x y).trace ^ 2 - 4 * (lin γ x y).det = y ^ 2 * (γ.trace ^ 2 - 4 * γ.det) := by
  rw [trace_lin, det_lin]; ring

theorem sq_eq_fin_two (γ : Matrix (Fin 2) (Fin 2) F) : γ * γ = γ.trace • γ - γ.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  conv_lhs => rw [eta_fin_two γ]
  rw [Matrix.mul_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply, Matrix.sub_apply] <;> ring

theorem lin_mul_lin (γ : Matrix (Fin 2) (Fin 2) F) (x y x' y' : F) :
    lin γ x y * lin γ x' y' = lin γ (x * x' - γ.det * y * y') (x * y' + x' * y + γ.trace * y * y') := by
  simp only [lin, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, sq_eq_fin_two, smul_sub]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

theorem lin_comm (γ : Matrix (Fin 2) (Fin 2) F) (x y x' y' : F) :
    lin γ x y * lin γ x' y' = lin γ x' y' * lin γ x y := by
  rw [lin_mul_lin, lin_mul_lin]; congr 1 <;> ring

theorem self_eq_lin (γ : Matrix (Fin 2) (Fin 2) F) : γ = lin γ 0 1 := by simp [lin]

theorem one_eq_lin (γ : Matrix (Fin 2) (Fin 2) F) : (1 : Matrix (Fin 2) (Fin 2) F) = lin γ 1 0 := by simp [lin]

theorem lin_lin_eq_self (γ : Matrix (Fin 2) (Fin 2) F) (x y : F) (hy : y ≠ 0) :
    lin (lin γ x y) (-(x / y)) (1 / y) = γ := by
  ext i j
  simp only [lin_apply]
  field_simp
  ring

theorem commute_lin_of_commute (γ M : Matrix (Fin 2) (Fin 2) F) (x y : F)
    (h : γ * M = M * γ) : lin γ x y * M = M * lin γ x y := by
  simp only [lin, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, h]

theorem commute_of_commute_lin (γ M : Matrix (Fin 2) (Fin 2) F) (x y : F) (hy : y ≠ 0)
    (h : lin γ x y * M = M * lin γ x y) : γ * M = M * γ := by
  have e := lin_lin_eq_self γ x y hy
  have := commute_lin_of_commute (lin γ x y) M (-(x / y)) (1 / y) h
  rwa [e] at this

variable (γ₀ : GL (Fin 2) F) (hreg : IsRegularSemisimple γ₀)
  (hns : ∀ g : GL (Fin 2) F,
    ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧
       ((g⁻¹ * γ₀ * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0))

include hreg hns

theorem false_of_diagonalises (P : Matrix (Fin 2) (Fin 2) F) (hP : P.det ≠ 0) (l l' : F)
    (h : (γ₀ : Matrix (Fin 2) (Fin 2) F) * P = P * !![l, 0; 0, l']) : False := by
  apply hns (Matrix.GeneralLinearGroup.mkOfDetNeZero P hP)
  have hc : (((Matrix.GeneralLinearGroup.mkOfDetNeZero P hP)⁻¹ * γ₀ * Matrix.GeneralLinearGroup.mkOfDetNeZero P hP :
      GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![l, 0; 0, l'] := by
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, mul_assoc]
    show P⁻¹ * ((γ₀ : Matrix (Fin 2) (Fin 2) F) * P) = _
    rw [h, ← mul_assoc, Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.mpr hP), one_mul]
  rw [hc]
  simp

omit hreg in
theorem entry01_ne_zero' (hreg : IsRegularSemisimple γ₀) : (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0 := by
  intro hb
  set a := (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 0
  set c := (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0
  set d := (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 1
  have hγ : (γ₀ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; c, d] := by
    rw [eta_fin_two (γ₀ : Matrix (Fin 2) (Fin 2) F), hb]
  have had : a - d ≠ 0 := by
    have h := (isRegularSemisimple_iff_ne_zero γ₀).mp hreg
    rw [hγ, Matrix.trace_fin_two_of, Matrix.det_fin_two_of] at h
    intro h0
    apply h
    rw [show (a + d) ^ 2 - 4 * (a * d - 0 * c) = (a - d) ^ 2 by ring, h0]; ring
  refine false_of_diagonalises γ₀ hreg hns !![a - d, 0; c, 1] ?_ a d ?_
  · rw [Matrix.det_fin_two_of]; simpa using had
  · rw [hγ, Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

theorem entry01_ne_zero : (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0 := entry01_ne_zero' γ₀ hns hreg

theorem charpoly_ne_zero (l : F) :
    l ^ 2 - (γ₀ : Matrix (Fin 2) (Fin 2) F).trace * l + (γ₀ : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
  intro hl
  have hb := entry01_ne_zero γ₀ hreg hns
  set a := (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 0 with ha
  set b := (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 1 with hb'
  set c := (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0 with hc
  set d := (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 1 with hd
  have hγ : (γ₀ : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] := eta_fin_two _
  rw [hγ, Matrix.trace_fin_two_of, Matrix.det_fin_two_of] at hl
  have hdisc : (a + d - 2 * l) ≠ 0 := by
    have h := (isRegularSemisimple_iff_ne_zero γ₀).mp hreg
    rw [hγ, Matrix.trace_fin_two_of, Matrix.det_fin_two_of] at h
    intro h0
    apply h
    have : (a + d) ^ 2 - 4 * (a * d - b * c) = (a + d - 2 * l) ^ 2 - 4 * (l ^ 2 - (a + d) * l + (a * d - b * c)) := by ring
    rw [this, h0, hl]; ring

  refine false_of_diagonalises γ₀ hreg hns !![b, b; l - a, a + d - l - a] ?_ l (a + d - l) ?_
  · rw [Matrix.det_fin_two_of]
    have : b * (a + d - l - a) - b * (l - a) = b * (a + d - 2 * l) := by ring
    rw [this]; exact mul_ne_zero hb hdisc
  · rw [hγ, Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j
    · simp; ring
    · simp; ring
    · simp; linear_combination (-1 : F) * hl
    · simp; linear_combination (-1 : F) * hl

theorem det_lin_ne_zero (x y : F) (h : ¬ (x = 0 ∧ y = 0)) : (lin (γ₀ : Matrix (Fin 2) (Fin 2) F) x y).det ≠ 0 := by
  rw [det_lin]
  by_cases hy : y = 0
  · subst hy
    have hx : x ≠ 0 := fun hx => h ⟨hx, rfl⟩
    simpa using pow_ne_zero 2 hx
  · intro h0
    apply charpoly_ne_zero γ₀ hreg hns (-(x / y))
    field_simp
    linear_combination h0

theorem det_lin_ne_zero_of_ne_zero (x y : F) (hy : y ≠ 0) : (lin (γ₀ : Matrix (Fin 2) (Fin 2) F) x y).det ≠ 0 :=
  det_lin_ne_zero γ₀ hreg hns x y fun h => hy h.2

omit hreg hns in
theorem smul_lin (γ : Matrix (Fin 2) (Fin 2) F) (a x y : F) : a • lin γ x y = lin γ (a * x) (a * y) := by
  simp only [lin, smul_add, smul_smul]

omit hreg hns in
theorem lin_add_lin (γ : Matrix (Fin 2) (Fin 2) F) (x y x' y' : F) : lin γ x y + lin γ x' y' = lin γ (x + x') (y + y') := by
  simp only [lin, add_smul]; abel

omit hreg hns in
theorem lin_sub_smul_one (γ : Matrix (Fin 2) (Fin 2) F) (x y b : F) :
    lin γ x y - b • (1 : Matrix (Fin 2) (Fin 2) F) = lin γ (x - b) y := by
  simp only [lin, sub_smul]; abel

omit hreg hns in

theorem disc_lin_ne_zero {γ : Matrix (Fin 2) (Fin 2) F} (h : γ.trace ^ 2 - 4 * γ.det ≠ 0) (x y : F) (hy : y ≠ 0) :
    (lin γ x y).trace ^ 2 - 4 * (lin γ x y).det ≠ 0 := by
  rw [disc_lin]; exact mul_ne_zero (pow_ne_zero 2 hy) h

omit hreg in

theorem eq_lin_of_commute (hreg : IsRegularSemisimple γ₀) (M : Matrix (Fin 2) (Fin 2) F)
    (h : (γ₀ : Matrix (Fin 2) (Fin 2) F) * M = M * (γ₀ : Matrix (Fin 2) (Fin 2) F)) :
    M = lin (γ₀ : Matrix (Fin 2) (Fin 2) F)
      (M 0 0 - M 0 1 * (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 0 / (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 1)
      (M 0 1 / (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 1) := by
  have hb := entry01_ne_zero' γ₀ hns hreg
  set a := (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 0 with ha
  set b := (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 1 with hb'
  set c := (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0 with hc
  set d := (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 1 with hd
  set p := M 0 0 with hp
  set q := M 0 1 with hq
  set r := M 1 0 with hr
  set s := M 1 1 with hs
  have hγ : (γ₀ : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] := eta_fin_two _
  have hM : M = !![p, q; r, s] := eta_fin_two _
  rw [hγ, hM, Matrix.mul_fin_two, Matrix.mul_fin_two] at h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  simp at h00 h01 h10

  have hr' : r = q * c / b := by field_simp; linear_combination h00
  have hs' : s = p - q * (a - d) / b := by field_simp; linear_combination h01
  rw [hM, lin_eq, hγ]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.empty_val']
  ext i j; fin_cases i <;> fin_cases j <;> simp [hr', hs'] <;> field_simp <;> ring

theorem exists_eq_lin_of_commute (M : Matrix (Fin 2) (Fin 2) F)
    (h : (γ₀ : Matrix (Fin 2) (Fin 2) F) * M = M * (γ₀ : Matrix (Fin 2) (Fin 2) F)) :
    ∃ x y : F, M = lin (γ₀ : Matrix (Fin 2) (Fin 2) F) x y :=
  ⟨_, _, eq_lin_of_commute γ₀ hns hreg M h⟩

theorem lin_inj {x y x' y' : F} (h : lin (γ₀ : Matrix (Fin 2) (Fin 2) F) x y = lin (γ₀ : Matrix (Fin 2) (Fin 2) F) x' y') :
    x = x' ∧ y = y' := by
  have hb := entry01_ne_zero γ₀ hreg hns
  have h01 := congrFun (congrFun h 0) 1
  have h00 := congrFun (congrFun h 0) 0
  simp only [lin_apply, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), Matrix.one_apply_eq, mul_zero, zero_add,
    mul_one] at h01 h00
  have hy : y = y' := mul_right_cancel₀ hb h01
  subst hy
  exact ⟨by linear_combination h00, rfl⟩

end Algebra

section Local

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
variable (γ₀ : GL (Fin 2) (v.adicCompletion K)) (hreg : IsRegularSemisimple γ₀)
  (hns : ∀ g : GL (Fin 2) (v.adicCompletion K),
    ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
       ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0))

theorem mem_localCentralizer_iff_commute (g : GL (Fin 2) (v.adicCompletion K)) :
    g ∈ localCentralizer K v γ₀ ↔
      (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) * g = g * (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
  rw [localCentralizer, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h; have := congrArg Units.val h; simpa [Units.val_mul] using this.symm
  · intro h; exact Units.ext (by simpa [Units.val_mul] using h.symm)

include hreg hns in

theorem mem_localCentralizer_iff (g : GL (Fin 2) (v.adicCompletion K)) :
    g ∈ localCentralizer K v γ₀ ↔ ∃ x y : v.adicCompletion K,
      (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = lin (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) x y := by
  rw [mem_localCentralizer_iff_commute]
  constructor
  · exact exists_eq_lin_of_commute γ₀ hreg hns _
  · rintro ⟨x, y, h⟩
    rw [h]
    exact (commute_lin_of_commute _ _ x y rfl).symm

theorem isCompact_closedBall_one : IsCompact {l : v.adicCompletion K | ‖l‖ ≤ 1} := by
  have : {l : v.adicCompletion K | ‖l‖ ≤ 1} = Metric.closedBall 0 1 := by
    ext l; simp
  rw [this]; exact isCompact_closedBall 0 1

include hreg hns in

theorem exists_pos_forall_le_norm_charpoly :
    ∃ c : ℝ, 0 < c ∧ ∀ l : v.adicCompletion K,
      c ≤ ‖l ^ 2 - (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace * l +
          (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ ∧
      c * ‖l‖ ^ 2 ≤ ‖l ^ 2 - (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace * l +
          (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ := by
  set t := (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace with ht
  set n := (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det with hn
  let χ : v.adicCompletion K → ℝ := fun l => ‖l ^ 2 - t * l + n‖
  let ρ : v.adicCompletion K → ℝ := fun m => ‖1 - t * m + n * m ^ 2‖
  have hχc : Continuous χ := by fun_prop
  have hρc : Continuous ρ := by fun_prop
  have hχ0 : ∀ l, 0 < χ l := fun l => norm_pos_iff.mpr (charpoly_ne_zero γ₀ hreg hns l)
  have hρ0 : ∀ m, 0 < ρ m := by
    intro m
    refine norm_pos_iff.mpr fun h0 => ?_
    by_cases hm : m = 0
    · subst hm; simp at h0
    · apply charpoly_ne_zero γ₀ hreg hns m⁻¹
      have : m⁻¹ ^ 2 - t * m⁻¹ + n = m⁻¹ ^ 2 * (1 - t * m + n * m ^ 2) := by field_simp
      rw [this, h0, mul_zero]
  have hB := isCompact_closedBall_one K v
  have hne : ({l : v.adicCompletion K | ‖l‖ ≤ 1}).Nonempty := ⟨0, by simp⟩
  obtain ⟨l₁, -, hmin₁⟩ := hB.exists_isMinOn hne hχc.continuousOn
  obtain ⟨m₂, -, hmin₂⟩ := hB.exists_isMinOn hne hρc.continuousOn
  set c := min (χ l₁) (ρ m₂) with hc
  have hcpos : 0 < c := lt_min (hχ0 l₁) (hρ0 m₂)
  refine ⟨c, hcpos, fun l => ?_⟩
  show c ≤ χ l ∧ c * ‖l‖ ^ 2 ≤ χ l
  by_cases hl : ‖l‖ ≤ 1
  · have h1 : c ≤ χ l := (min_le_left _ _).trans (hmin₁ hl)
    refine ⟨h1, ?_⟩
    have hl2 : ‖l‖ ^ 2 ≤ 1 := by
      rw [sq_le_one_iff₀ (norm_nonneg l)]; exact hl
    calc c * ‖l‖ ^ 2 ≤ c * 1 := mul_le_mul_of_nonneg_left hl2 hcpos.le
      _ = c := mul_one c
      _ ≤ χ l := h1
  · push Not at hl
    have hl0 : l ≠ 0 := by rintro rfl; rw [norm_zero] at hl; linarith
    have hinv : ‖l⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hl.le
    have h2 : c ≤ ρ l⁻¹ := (min_le_right _ _).trans (hmin₂ hinv)
    have hfac : l ^ 2 - t * l + n = l ^ 2 * (1 - t * l⁻¹ + n * l⁻¹ ^ 2) := by field_simp
    have hχl : χ l = ‖l‖ ^ 2 * ρ l⁻¹ := by
      show ‖l ^ 2 - t * l + n‖ = ‖l‖ ^ 2 * ‖1 - t * l⁻¹ + n * l⁻¹ ^ 2‖
      rw [hfac, norm_mul, norm_pow]
    have hl1 : 1 ≤ ‖l‖ ^ 2 := by nlinarith
    rw [hχl]
    constructor
    · calc c = 1 * c := (one_mul _).symm
        _ ≤ ‖l‖ ^ 2 * ρ l⁻¹ := mul_le_mul hl1 h2 hcpos.le (by positivity)
    · rw [mul_comm]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)

include hreg hns in

theorem exists_forall_sq_le_mul_norm_det_lin :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : v.adicCompletion K,
      ‖x‖ ^ 2 ≤ C * ‖(lin (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) x y).det‖ ∧
      ‖y‖ ^ 2 ≤ C * ‖(lin (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) x y).det‖ := by
  obtain ⟨c, hc, hχ⟩ := exists_pos_forall_le_norm_charpoly K v γ₀ hreg hns
  refine ⟨max 1 c⁻¹, lt_max_of_lt_left one_pos, fun x y => ?_⟩
  set t := (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace with ht
  set n := (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det with hn
  have hQ0 : 0 ≤ ‖(lin (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) x y).det‖ := norm_nonneg _
  have conv : ∀ a : ℝ, c * a ≤ ‖(lin (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) x y).det‖ →
      a ≤ max 1 c⁻¹ * ‖(lin (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) x y).det‖ := by
    intro a h
    calc a ≤ ‖(lin (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) x y).det‖ / c := (le_div_iff₀' hc).mpr h
      _ = c⁻¹ * _ := div_eq_inv_mul _ _
      _ ≤ max 1 c⁻¹ * _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hQ0
  by_cases hy : y = 0
  · subst hy
    have hdet : (lin (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) x 0).det = x ^ 2 := by rw [det_lin]; ring
    rw [hdet, norm_pow, norm_zero, zero_pow two_ne_zero]
    refine ⟨?_, by positivity⟩
    calc ‖x‖ ^ 2 = 1 * ‖x‖ ^ 2 := (one_mul _).symm
      _ ≤ max 1 c⁻¹ * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · refine ⟨conv _ ?_, conv _ ?_⟩ <;> rw [det_lin]
    · have hfac : x ^ 2 + t * x * y + n * y ^ 2 = y ^ 2 * ((-(x / y)) ^ 2 - t * (-(x / y)) + n) := by
        field_simp; ring
      rw [hfac, norm_mul, norm_pow]
      calc c * ‖x‖ ^ 2 = ‖y‖ ^ 2 * (c * ‖-(x / y)‖ ^ 2) := by
            rw [norm_neg, norm_div, div_pow]; field_simp
        _ ≤ ‖y‖ ^ 2 * ‖(-(x / y)) ^ 2 - t * -(x / y) + n‖ := mul_le_mul_of_nonneg_left (hχ _).2 (by positivity)
    · have hfac : x ^ 2 + t * x * y + n * y ^ 2 = y ^ 2 * ((-(x / y)) ^ 2 - t * (-(x / y)) + n) := by
        field_simp; ring
      rw [hfac, norm_mul, norm_pow, mul_comm]
      exact mul_le_mul_of_nonneg_left (hχ _).1 (by positivity)

end Local

end Ws31.Torus

end

namespace Ws31
namespace Torus

section Saturated

open AutomorphicForm Matrix

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
variable (γ₀ : GL (Fin 2) (v.adicCompletion K)) (hreg : IsRegularSemisimple γ₀)
  (hns : ∀ g : GL (Fin 2) (v.adicCompletion K),
    ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
       ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0))

omit γ₀ in

theorem exists_valued_eq_ofAdd {a : v.adicCompletion K} (ha : a ≠ 0) :
    ∃ j : ℤ, Valued.v a = ((Multiplicative.ofAdd j : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h0 : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
  obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.mp h0
  exact ⟨Multiplicative.toAdd g, by rw [ofAdd_toAdd]; exact hg.symm⟩

omit γ₀ in
theorem valued_pow_uniformizer (ϖ : v.adicCompletion K)
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) (m : ℕ) :
    Valued.v (ϖ ^ m) = ((Multiplicative.ofAdd (-(m : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rw [map_pow, hϖ, ← WithZero.coe_pow, ← ofAdd_nsmul, smul_neg, nsmul_eq_mul, mul_one]

omit γ₀ in
theorem uniformizer_ne_zero (ϖ : v.adicCompletion K)
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) : ϖ ≠ 0 := by
  intro h; rw [h, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ

omit γ₀ in

theorem norm_le_norm_iff_valued {a b : v.adicCompletion K} (hb : b ≠ 0) : ‖a‖ ≤ ‖b‖ ↔ Valued.v a ≤ Valued.v b := by
  have hb' : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hvb : Valued.v b ≠ 0 := (Valuation.ne_zero_iff _).mpr hb
  rw [← div_le_one hb', ← norm_div, Valued.toNormedField.norm_le_one_iff, map_div₀, div_le_one₀ (zero_lt_iff.mpr hvb)]

include hreg hns in

theorem exists_saturated_generator (ϖ : v.adicCompletion K)
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    ∃ x₀ y₀ : v.adicCompletion K, y₀ ≠ 0 ∧
      (Valued.v (lin (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) x₀ y₀).det ≤ 1 ∧
        Valued.v (lin (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) x₀ y₀).trace ≤ 1) ∧
      (∀ b : v.adicCompletion K, Valued.v b ≤ 1 →
        ¬ (Valued.v (lin (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) x₀ y₀ -
              b • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))).det ≤ Valued.v ϖ ^ 2 ∧
           Valued.v (lin (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) x₀ y₀ -
              b • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))).trace ≤ Valued.v ϖ)) := by
  have hϖ0 := uniformizer_ne_zero K v ϖ hϖ
  set G := (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) with hG

  let IsInt : v.adicCompletion K → v.adicCompletion K → Prop := fun x y =>
    Valued.v (lin G x y).det ≤ 1 ∧ Valued.v (lin G x y).trace ≤ 1
  let P : ℤ → Prop := fun k => ∃ x y, IsInt x y ∧ y ≠ 0 ∧
    Valued.v y = ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero (Multiplicative ℤ))

  obtain ⟨C, hC, hco⟩ := exists_forall_sq_le_mul_norm_det_lin K v γ₀ hreg hns
  have hnϖ : ‖ϖ‖ < 1 := Valued.toNormedField.norm_lt_one_iff.mpr (by
    rw [hϖ, ← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt]; norm_num)
  have hnϖi : 1 < ‖ϖ⁻¹‖ := by rw [norm_inv]; exact one_lt_inv₀ (norm_pos_iff.mpr hϖ0) |>.mpr hnϖ
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (Real.sqrt C) hnϖi
  have hbdd : ∀ k, P k → k ≤ (N : ℤ) := by
    rintro k ⟨x, y, ⟨hd, -⟩, hy0, hvy⟩
    have hy2 : ‖y‖ ^ 2 ≤ C := by
      have := (hco x y).2
      have hd' : ‖(lin G x y).det‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.mpr hd
      nlinarith
    have hy : ‖y‖ ≤ Real.sqrt C := by rw [← Real.sqrt_sq (norm_nonneg y)]; exact Real.sqrt_le_sqrt hy2
    have hlt : ‖y‖ ≤ ‖ϖ⁻¹ ^ N‖ := by rw [norm_pow]; exact hy.trans hN.le
    rw [norm_le_norm_iff_valued K v (pow_ne_zero _ (inv_ne_zero hϖ0)), hvy, inv_pow, map_inv₀,
      valued_pow_uniformizer K v ϖ hϖ, ← WithZero.coe_inv, WithZero.coe_le_coe, ← ofAdd_neg, neg_neg,
      Multiplicative.ofAdd_le] at hlt
    exact hlt

  obtain ⟨jd, hjd⟩ := exists_valued_eq_ofAdd K v (a := G.det)
    (by rw [hG, ← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det γ₀).ne_zero)
  have hex : ∃ k, P k := by

    obtain ⟨m, hm⟩ : ∃ m : ℕ, Valued.v (G.det * (ϖ ^ m) ^ 2) ≤ 1 ∧ Valued.v (G.trace * ϖ ^ m) ≤ 1 := by
      by_cases ht : G.trace = 0
      · refine ⟨jd.toNat, ?_, by rw [ht, zero_mul, map_zero]; exact zero_le'⟩
        rw [map_mul, map_pow, hjd, valued_pow_uniformizer K v ϖ hϖ, ← WithZero.coe_pow, ← WithZero.coe_mul,
          ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_nsmul, ← ofAdd_add, ← ofAdd_zero, Multiplicative.ofAdd_le]
        have := Int.self_le_toNat jd
        simp only [smul_neg, nsmul_eq_mul, Nat.cast_ofNat]
        omega
      · obtain ⟨jt, hjt⟩ := exists_valued_eq_ofAdd K v ht
        refine ⟨(max jd jt).toNat, ?_, ?_⟩
        · rw [map_mul, map_pow, hjd, valued_pow_uniformizer K v ϖ hϖ, ← WithZero.coe_pow, ← WithZero.coe_mul,
            ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_nsmul, ← ofAdd_add, ← ofAdd_zero, Multiplicative.ofAdd_le]
          have := Int.self_le_toNat (max jd jt)
          have := le_max_left jd jt
          simp only [smul_neg, nsmul_eq_mul, Nat.cast_ofNat]
          omega
        · rw [map_mul, hjt, valued_pow_uniformizer K v ϖ hϖ, ← WithZero.coe_mul,
            ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_add, ← ofAdd_zero, Multiplicative.ofAdd_le]
          have := Int.self_le_toNat (max jd jt)
          have := le_max_right jd jt
          omega
    refine ⟨-(m : ℤ), 0, ϖ ^ m, ⟨?_, ?_⟩, pow_ne_zero _ hϖ0, valued_pow_uniformizer K v ϖ hϖ m⟩
    · rw [det_lin]; simpa using hm.1
    · rw [trace_lin]; simpa using hm.2

  obtain ⟨k₀, ⟨x₀, y₀, hint, hy0, hvy₀⟩, hmax⟩ := Int.exists_greatest_of_bdd ⟨N, hbdd⟩ hex
  refine ⟨x₀, y₀, hy0, hint, fun b _ hb => ?_⟩

  have hP : P (k₀ + 1) := by
    refine ⟨ϖ⁻¹ * (x₀ - b), ϖ⁻¹ * y₀, ⟨?_, ?_⟩, mul_ne_zero (inv_ne_zero hϖ0) hy0, ?_⟩
    · rw [← smul_lin, Matrix.det_smul, Fintype.card_fin, ← lin_sub_smul_one, map_mul, map_pow, map_inv₀]
      have h := hb.1
      have hv0 : Valued.v ϖ ≠ 0 := (Valuation.ne_zero_iff _).mpr hϖ0
      calc (Valued.v ϖ)⁻¹ ^ 2 * Valued.v (lin G x₀ y₀ - b • 1).det ≤ (Valued.v ϖ)⁻¹ ^ 2 * Valued.v ϖ ^ 2 :=
            mul_le_mul_right h _
        _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hv0, one_pow]
    · rw [← smul_lin, Matrix.trace_smul, smul_eq_mul, ← lin_sub_smul_one, map_mul, map_inv₀]
      have h := hb.2
      have hv0 : Valued.v ϖ ≠ 0 := (Valuation.ne_zero_iff _).mpr hϖ0
      calc (Valued.v ϖ)⁻¹ * Valued.v (lin G x₀ y₀ - b • 1).trace ≤ (Valued.v ϖ)⁻¹ * Valued.v ϖ :=
            mul_le_mul_right h _
        _ = 1 := inv_mul_cancel₀ hv0
    · rw [map_mul, map_inv₀, hϖ, hvy₀, ← WithZero.coe_inv, ← WithZero.coe_mul, ← ofAdd_neg, ← ofAdd_add, neg_neg,
        add_comm]
  have := hmax _ hP
  omega

end Saturated

end Ws31.Torus

namespace Ws31
namespace Torus

open AutomorphicForm Matrix

section Depth

variable {F : Type*} [Field F]

theorem one_add_smul_lin (γ : Matrix (Fin 2) (Fin 2) F) (t x₀ y₀ : F) :
    (1 : F) • (1 : Matrix (Fin 2) (Fin 2) F) + t • lin γ x₀ y₀ = lin γ (1 + t * x₀) (t * y₀) := by
  rw [smul_lin, one_eq_lin γ, smul_lin, lin_add_lin]; simp

theorem det_lin_one_add (γ : Matrix (Fin 2) (Fin 2) F) (t x₀ y₀ : F) :
    (lin γ (1 + t * x₀) (t * y₀)).det = 1 + t * (lin γ x₀ y₀).trace + t ^ 2 * (lin γ x₀ y₀).det := by
  rw [det_lin, det_lin, trace_lin]; ring

end Depth

section DepthLocal

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => v.adicCompletion K

theorem valued_ne_zero_of_uniformizer (ϖ : Kv) (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ)) : ϖ ≠ 0 := by
  intro h; rw [h, Valuation.map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ

theorem valued_det_one_add (ϖ : Kv) (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ)) (m : ℕ) (hm : 1 ≤ m)
    (T D : Kv) (hT : Valued.v T ≤ 1) (hD : Valued.v D ≤ 1) :
    Valued.v (1 + ϖ ^ m * T + (ϖ ^ m) ^ 2 * D) = 1 := by
  have hϖ1 : Valued.v ϖ < 1 := by rw [hϖ]; exact_mod_cast (show Multiplicative.ofAdd (-1 : ℤ) < 1 by decide)
  have hϖm : Valued.v (ϖ ^ m) < 1 := by
    rw [Valuation.map_pow]; exact pow_lt_one₀ zero_le' hϖ1 (by omega)
  have h1 : Valued.v (ϖ ^ m * T) < 1 := by
    rw [Valuation.map_mul]; exact mul_lt_one_of_lt_of_le hϖm hT
  have h2 : Valued.v ((ϖ ^ m) ^ 2 * D) < 1 := by
    rw [Valuation.map_mul, Valuation.map_pow]
    exact mul_lt_one_of_lt_of_le (pow_lt_one₀ zero_le' hϖm two_ne_zero) hD
  have h12 : Valued.v (ϖ ^ m * T + (ϖ ^ m) ^ 2 * D) < 1 :=
    lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt h1 h2)
  rw [add_assoc]
  exact Valued.v.map_one_add_of_lt h12

end DepthLocal

end Ws31.Torus

namespace Ws31
namespace Torus

open AutomorphicForm Matrix Filter Topology

section DepthMain

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => v.adicCompletion K
local notation "M2" => Matrix (Fin 2) (Fin 2) (v.adicCompletion K)

theorem lin_mul_conj {F : Type*} [Field F] (γ : Matrix (Fin 2) (Fin 2) F) (a b : F) :
    lin γ a b * lin γ (a + γ.trace * b) (-b) = (lin γ a b).det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  rw [lin_mul_lin, det_lin, one_eq_lin γ, smul_lin]
  congr 1 <;> ring

theorem scalar_val (a : Kvˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) a : GL (Fin 2) Kv) : M2) = (a : Kv) • (1 : M2) := by
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_apply, Matrix.one_apply]
  rfl

set_option maxHeartbeats 3200000 in
theorem depth_main (c : Kvˣ) (ϖ : Kv) (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (γ₀ : GL (Fin 2) Kv) (hreg : IsRegularSemisimple γ₀)
    (hns : ∀ g : GL (Fin 2) Kv, ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) Kv) : M2) 0 1 = 0 ∧ ((g⁻¹ * γ₀ * g : GL (Fin 2) Kv) : M2) 1 0 = 0))
    (hgen : ∃ x₀ y₀ : Kv, y₀ ≠ 0 ∧
      (Valued.v (lin (γ₀ : M2) x₀ y₀).det ≤ 1 ∧ Valued.v (lin (γ₀ : M2) x₀ y₀).trace ≤ 1) ∧
      (∀ b : Kv, Valued.v b ≤ 1 →
        ¬ (Valued.v (lin (γ₀ : M2) x₀ y₀ - b • 1).det ≤ Valued.v ϖ ^ 2 ∧ Valued.v (lin (γ₀ : M2) x₀ y₀ - b • 1).trace ≤ Valued.v ϖ))) :
    ∃ (Y : M2) (γ : ℕ → GL (Fin 2) Kv),
      (Valued.v Y.det ≤ 1 ∧ Valued.v Y.trace ≤ 1) ∧
      (∀ b : Kv, Valued.v b ≤ 1 →
        ¬ (Valued.v (Y - b • 1).det ≤ Valued.v ϖ ^ 2 ∧ Valued.v (Y - b • 1).trace ≤ Valued.v ϖ)) ∧
      (∀ m : ℕ, 1 ≤ m →
        γ m ∈ localCentralizer K v γ₀ ∧ IsRegularSemisimple (γ m) ∧
        Valued.v ((((c⁻¹ : Kvˣ) : Kv) • ((γ m : GL (Fin 2) Kv) : M2)).det) = 1 ∧
        ((c⁻¹ : Kvˣ) : Kv) • ((γ m : GL (Fin 2) Kv) : M2) = (1 : Kv) • 1 + (ϖ ^ m) • Y ∧
        localCentralizer K v (γ m) = localCentralizer K v γ₀) ∧
      Tendsto γ atTop (nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) := by
  obtain ⟨x₀, y₀, hy₀, hYint, hYgen⟩ := hgen
  have hϖ0 : ϖ ≠ 0 := valued_ne_zero_of_uniformizer K v ϖ hϖ
  have hc0 : (c : Kv) ≠ 0 := c.ne_zero
  have hdisc : (γ₀ : M2).trace ^ 2 - 4 * (γ₀ : M2).det ≠ 0 := (isRegularSemisimple_iff_ne_zero γ₀).mp hreg

  set L : ℕ → M2 := fun m => lin (γ₀ : M2) (1 + ϖ ^ m * x₀) (ϖ ^ m * y₀) with hL
  have hyc : ∀ m, (c : Kv) * (ϖ ^ m * y₀) ≠ 0 := fun m => mul_ne_zero hc0 (mul_ne_zero (pow_ne_zero m hϖ0) hy₀)
  have hLdet : ∀ m, (L m).det ≠ 0 := fun m =>
    det_lin_ne_zero_of_ne_zero γ₀ hreg hns _ _ (mul_ne_zero (pow_ne_zero m hϖ0) hy₀)
  have hMdet : ∀ m, ((c : Kv) • L m).det ≠ 0 := fun m => by
    rw [Matrix.det_smul, Fintype.card_fin]; exact mul_ne_zero (pow_ne_zero _ hc0) (hLdet m)
  set γ : ℕ → GL (Fin 2) Kv := fun m => Matrix.GeneralLinearGroup.mkOfDetNeZero ((c : Kv) • L m) (hMdet m) with hγ
  have hγval : ∀ m, ((γ m : GL (Fin 2) Kv) : M2) = (c : Kv) • L m := fun m => rfl
  have hγlin : ∀ m, ((γ m : GL (Fin 2) Kv) : M2) = lin (γ₀ : M2) ((c : Kv) * (1 + ϖ ^ m * x₀)) ((c : Kv) * (ϖ ^ m * y₀)) :=
    fun m => by rw [hγval, hL, smul_lin]
  have hcL : ∀ m, ((c⁻¹ : Kvˣ) : Kv) • ((γ m : GL (Fin 2) Kv) : M2) = L m := fun m => by
    rw [hγval, smul_smul, Units.val_inv_eq_inv_val, inv_mul_cancel₀ hc0, one_smul]
  refine ⟨lin (γ₀ : M2) x₀ y₀, γ, hYint, hYgen, fun m hm => ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    exact (mem_localCentralizer_iff K v γ₀ hreg hns (γ m)).mpr ⟨_, _, hγlin m⟩
  ·
    rw [isRegularSemisimple_iff_ne_zero, hγlin]
    exact disc_lin_ne_zero hdisc _ _ (hyc m)
  ·
    rw [hcL, hL, det_lin_one_add]
    exact valued_det_one_add K v ϖ hϖ m hm _ _ hYint.2 hYint.1
  ·
    rw [hcL, hL, one_add_smul_lin]
  ·
    ext g
    rw [mem_localCentralizer_iff_commute, mem_localCentralizer_iff_commute, hγlin]
    exact ⟨fun h => commute_of_commute_lin _ _ _ _ (hyc m) h, fun h => commute_lin_of_commute _ _ _ _ h⟩
  ·
    have hpow : Tendsto (fun m : ℕ => ϖ ^ m) atTop (nhds (0 : Kv)) :=
      Valued.tendsto_zero_pow_of_v_lt_one (by rw [hϖ]; exact_mod_cast (show Multiplicative.ofAdd (-1 : ℤ) < 1 by decide))

    have hval : Tendsto (fun m => ((γ m : GL (Fin 2) Kv) : M2)) atTop
        (nhds ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) Kv) : M2)) := by
      have hf : Continuous fun t : Kv => (c : Kv) • ((1 : Kv) • (1 : M2) + t • lin (γ₀ : M2) x₀ y₀) := by fun_prop
      have e : (fun m => ((γ m : GL (Fin 2) Kv) : M2)) = (fun t : Kv => (c : Kv) • ((1 : Kv) • (1 : M2) + t • lin (γ₀ : M2) x₀ y₀)) ∘ fun m : ℕ => ϖ ^ m := by
        funext m
        show ((γ m : GL (Fin 2) Kv) : M2) = (c : Kv) • ((1 : Kv) • (1 : M2) + ϖ ^ m • lin (γ₀ : M2) x₀ y₀)
        rw [hγval, hL, one_add_smul_lin]
      have hlim0 : (c : Kv) • ((1 : Kv) • (1 : M2) + (0 : Kv) • lin (γ₀ : M2) x₀ y₀)
          = ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) Kv) : M2) := by
        rw [zero_smul, add_zero, one_smul, scalar_val]
      rw [e, ← hlim0]
      exact (hf.tendsto 0).comp hpow

    have hinv_eq : ∀ m, (((γ m)⁻¹ : GL (Fin 2) Kv) : M2) =
        ((c : Kv) * (L m).det)⁻¹ • lin (γ₀ : M2) ((1 + ϖ ^ m * x₀) + (γ₀ : M2).trace * (ϖ ^ m * y₀)) (-(ϖ ^ m * y₀)) := by
      intro m
      rw [Matrix.coe_units_inv, hγval]
      refine Matrix.inv_eq_right_inv ?_
      have hd : (lin (γ₀ : M2) (1 + ϖ ^ m * x₀) (ϖ ^ m * y₀)).det ≠ 0 := hLdet m
      show ((c : Kv) • lin (γ₀ : M2) (1 + ϖ ^ m * x₀) (ϖ ^ m * y₀)) *
          (((c : Kv) * (lin (γ₀ : M2) (1 + ϖ ^ m * x₀) (ϖ ^ m * y₀)).det)⁻¹ •
            lin (γ₀ : M2) ((1 + ϖ ^ m * x₀) + (γ₀ : M2).trace * (ϖ ^ m * y₀)) (-(ϖ ^ m * y₀))) = 1
      rw [smul_mul_smul_comm, mul_smul, lin_mul_conj, smul_smul, smul_smul]
      rw [show (c : Kv) * ((c : Kv) * (lin (γ₀ : M2) (1 + ϖ ^ m * x₀) (ϖ ^ m * y₀)).det)⁻¹ *
          (lin (γ₀ : M2) (1 + ϖ ^ m * x₀) (ϖ ^ m * y₀)).det = 1 by field_simp, one_smul]
    have hdetlim : Tendsto (fun m => (c : Kv) * (L m).det) atTop (nhds ((c : Kv) * 1)) := by
      have hf : Continuous fun t : Kv => (c : Kv) * (1 + t * (lin (γ₀ : M2) x₀ y₀).trace + t ^ 2 * (lin (γ₀ : M2) x₀ y₀).det) := by
        fun_prop
      have e : (fun m => (c : Kv) * (L m).det) =
          (fun t : Kv => (c : Kv) * (1 + t * (lin (γ₀ : M2) x₀ y₀).trace + t ^ 2 * (lin (γ₀ : M2) x₀ y₀).det)) ∘ fun m : ℕ => ϖ ^ m := by
        funext m
        show (c : Kv) * (L m).det = (c : Kv) * (1 + ϖ ^ m * (lin (γ₀ : M2) x₀ y₀).trace + (ϖ ^ m) ^ 2 * (lin (γ₀ : M2) x₀ y₀).det)
        rw [hL, det_lin_one_add]
      rw [e]
      have := (hf.tendsto 0).comp hpow
      simpa using this
    have hinvlim : Tendsto (fun m => (((γ m)⁻¹ : GL (Fin 2) Kv) : M2)) atTop
        (nhds (((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ : GL (Fin 2) Kv) : M2)) := by
      have e : (fun m => (((γ m)⁻¹ : GL (Fin 2) Kv) : M2)) = fun m =>
          ((c : Kv) * (L m).det)⁻¹ • lin (γ₀ : M2) ((1 + ϖ ^ m * x₀) + (γ₀ : M2).trace * (ϖ ^ m * y₀)) (-(ϖ ^ m * y₀)) :=
        funext hinv_eq
      have htarget : (((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ : GL (Fin 2) Kv) : M2) =
          ((c : Kv) * 1)⁻¹ • lin (γ₀ : M2) ((1 + 0 * x₀) + (γ₀ : M2).trace * (0 * y₀)) (-(0 * y₀)) := by
        rw [show ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ : GL (Fin 2) Kv) = Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹
          from (map_inv (Matrix.GeneralLinearGroup.scalar (Fin 2)) c).symm, scalar_val]
        simp only [mul_one, zero_mul, mul_zero, add_zero, neg_zero, Units.val_inv_eq_inv_val]
        rw [← one_eq_lin]
      rw [e, htarget]
      refine Tendsto.smul (hdetlim.inv₀ (by rw [mul_one]; exact hc0)) ?_
      have hf : Continuous fun t : Kv => lin (γ₀ : M2) ((1 + t * x₀) + (γ₀ : M2).trace * (t * y₀)) (-(t * y₀)) := by
        unfold lin; fun_prop
      exact (hf.tendsto 0).comp hpow

    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    exact hval.prodMk_nhds (MulOpposite.continuous_op.continuousAt.tendsto.comp hinvlim)

end DepthMain

end Ws31.Torus

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ) (ϖ : v.adicCompletion K)
    (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (γ₀ : GL (Fin 2) (v.adicCompletion K)) (_hreg : AutomorphicForm.IsRegularSemisimple γ₀)
    (_hns : ∀ g : GL (Fin 2) (v.adicCompletion K),
      ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
         ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0)) :
    ∃ (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) (γ : ℕ → GL (Fin 2) (v.adicCompletion K)),
      (Valued.v Y.det ≤ 1 ∧ Valued.v Y.trace ≤ 1) ∧
      (∀ b : v.adicCompletion K, Valued.v b ≤ 1 →
        ¬ (Valued.v (Y - b • 1).det ≤ Valued.v ϖ ^ 2 ∧ Valued.v (Y - b • 1).trace ≤ Valued.v ϖ)) ∧
      (∀ m : ℕ, 1 ≤ m →
        γ m ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
        AutomorphicForm.IsRegularSemisimple (γ m) ∧
        Valued.v ((((c⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) •
          ((γ m : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))).det) = 1 ∧
        ((c⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) •
            ((γ m : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
          = (1 : v.adicCompletion K) • 1 + (ϖ ^ m) • Y ∧
        AutomorphicForm.localCentralizer K v (γ m) = AutomorphicForm.localCentralizer K v γ₀) ∧
      Filter.Tendsto γ Filter.atTop (nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) :=
  Ws31.Torus.depth_main K v c ϖ hϖ γ₀ _hreg _hns (Ws31.Torus.exists_saturated_generator K v γ₀ _hreg _hns ϖ hϖ)

end S_AutomorphicForm_exists_generator_and_seq_mem_localCentralizer_tendsto_scalar_of_forall_not_diagonal
end P2MW
export P2MW.S_AutomorphicForm_exists_generator_and_seq_mem_localCentralizer_tendsto_scalar_of_forall_not_diagonal (solution)
