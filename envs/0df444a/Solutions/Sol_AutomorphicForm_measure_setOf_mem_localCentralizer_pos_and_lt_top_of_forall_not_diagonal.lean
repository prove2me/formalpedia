-- Prove2me | solution 1 for AutomorphicForm.measure_setOf_mem_localCentralizer_pos_and_lt_top_of_forall_not_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/4248f4ad-3325-59c4-b7cc-406fecd6df66

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_measure_setOf_mem_localCentralizer_pos_and_lt_top_of_forall_not_diagonal

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

section MeasureA

open AutomorphicForm Matrix MeasureTheory Topology

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
variable (γ₀ : GL (Fin 2) (v.adicCompletion K)) (hreg : IsRegularSemisimple γ₀)
  (hns : ∀ g : GL (Fin 2) (v.adicCompletion K),
    ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
       ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0))

theorem isClosed_localCentralizer :
    IsClosed (localCentralizer K v γ₀ : Set (GL (Fin 2) (v.adicCompletion K))) := by
  have : (localCentralizer K v γ₀ : Set (GL (Fin 2) (v.adicCompletion K))) =
      {g | g * γ₀ = γ₀ * g} := by
    ext g; exact Subgroup.mem_centralizer_singleton_iff
  rw [this]
  exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)

theorem norm_eq_one_iff_valued (x : v.adicCompletion K) : ‖x‖ = 1 ↔ Valued.v x = 1 := by
  constructor
  · intro h
    exact le_antisymm (Valued.toNormedField.norm_le_one_iff.mp h.le) (Valued.toNormedField.one_le_norm_iff.mp h.ge)
  · intro h
    exact le_antisymm (Valued.toNormedField.norm_le_one_iff.mpr h.le) (Valued.toNormedField.one_le_norm_iff.mpr h.ge)

theorem norm_eq_one_of_norm_sub_one_lt (a : v.adicCompletion K) (h : ‖a - 1‖ < 1) : ‖a‖ = 1 := by
  apply le_antisymm
  · calc ‖a‖ = ‖(a - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ max ‖a - 1‖ ‖(1 : v.adicCompletion K)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le h.le (by rw [norm_one])
  · by_contra hlt
    push Not at hlt
    have : ‖(1 : v.adicCompletion K)‖ < 1 :=
      calc ‖(1 : v.adicCompletion K)‖ = ‖a + (1 - a)‖ := by rw [add_sub_cancel]
        _ ≤ max ‖a‖ ‖1 - a‖ := IsUltrametricDist.norm_add_le_max _ _
        _ < 1 := max_lt hlt (by rwa [← norm_neg, neg_sub])
    rw [norm_one] at this
    exact lt_irrefl _ this

theorem norm_two_le_one : ‖(2 : v.adicCompletion K)‖ ≤ 1 := by
  rw [Valued.toNormedField.norm_le_one_iff, ← HeightOneSpectrum.mem_adicCompletionIntegers]
  exact_mod_cast natCast_mem (v.adicCompletionIntegers K) 2

omit γ₀ in

theorem norm_lin_apply_le (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) (x y : v.adicCompletion K) (R M : ℝ)
    (hR : 0 ≤ R) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hM : ∀ i j, ‖γ i j‖ ≤ M) (i j : Fin 2) :
    ‖lin γ x y i j‖ ≤ R * (1 + M) := by
  rw [lin_apply]
  have h1 : ‖(1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ≤ 1 := by
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq, norm_one]
    · rw [Matrix.one_apply_ne hij, norm_zero]; exact zero_le_one
  calc ‖x * (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j + y * γ i j‖
      ≤ ‖x‖ * ‖(1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ + ‖y‖ * ‖γ i j‖ :=
        (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
    _ ≤ R * 1 + R * M :=
        add_le_add (mul_le_mul hx h1 (norm_nonneg _) hR) (mul_le_mul hy (hM i j) (norm_nonneg _) hR)
    _ = R * (1 + M) := by ring

omit γ₀ in

theorem norm_inv_apply_le (g : GL (Fin 2) (v.adicCompletion K)) (R : ℝ)
    (hdet : ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ = 1)
    (h : ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ≤ R) (i j : Fin 2) :
    ‖((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ≤ R := by
  have hinv : ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det)⁻¹ •
        !![(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1, -(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1;
           -(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0] := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv']
  rw [hinv, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, hdet, inv_one, one_mul]
  fin_cases i <;> fin_cases j
  · simpa using h 1 1
  · simpa using h 0 1
  · simpa using h 1 0
  · simpa using h 0 0

include hreg hns in

theorem exists_forall_norm_entry_le :
    ∃ R : ℝ, 0 < R ∧ ∀ g : GL (Fin 2) (v.adicCompletion K), g ∈ localCentralizer K v γ₀ →
      ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ = 1 →
      (∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ≤ R) ∧
      (∀ i j, ‖((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ≤ R) := by
  obtain ⟨C, hC, hco⟩ := exists_forall_sq_le_mul_norm_det_lin K v γ₀ hreg hns
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ i j, ‖(γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ≤ M := by
    refine ⟨‖(γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0‖ + ‖(γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1‖ +
      ‖(γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0‖ + ‖(γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1‖, ?_⟩
    have h := fun i j => norm_nonneg ((γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j)
    have h00 := h 0 0; have h01 := h 0 1; have h10 := h 1 0; have h11 := h 1 1
    rw [Fin.forall_fin_two, Fin.forall_fin_two, Fin.forall_fin_two]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 0)
  have hsq : 0 ≤ Real.sqrt C := Real.sqrt_nonneg C
  refine ⟨Real.sqrt C * (1 + M) + 1, by positivity, fun g hg hdet => ?_⟩
  obtain ⟨x, y, hxy⟩ := (mem_localCentralizer_iff K v γ₀ hreg hns g).mp hg
  obtain ⟨hx2, hy2⟩ := hco x y
  rw [← hxy, hdet, mul_one] at hx2 hy2
  have hx : ‖x‖ ≤ Real.sqrt C := by rw [← Real.sqrt_sq (norm_nonneg x)]; exact Real.sqrt_le_sqrt hx2
  have hy : ‖y‖ ≤ Real.sqrt C := by rw [← Real.sqrt_sq (norm_nonneg y)]; exact Real.sqrt_le_sqrt hy2
  have hent : ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ≤ Real.sqrt C * (1 + M) + 1 := by
    intro i j
    rw [hxy]
    exact (norm_lin_apply_le K v _ x y _ M hsq hx hy hM i j).trans (le_add_of_nonneg_right zero_le_one)
  exact ⟨hent, norm_inv_apply_le K v g _ hdet hent⟩

include hreg hns in

theorem exists_isCompact_superset :
    ∃ C : Set (GL (Fin 2) (v.adicCompletion K)), IsCompact C ∧
      ∀ g : GL (Fin 2) (v.adicCompletion K), g ∈ localCentralizer K v γ₀ →
        Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 → g ∈ C := by
  obtain ⟨R, hR, hb⟩ := exists_forall_norm_entry_le K v γ₀ hreg hns
  refine ⟨integralUnitsSet {x : v.adicCompletion K | ‖x‖ ≤ R}, ?_, fun g hg hdet => ?_⟩
  · apply isCompact_integralUnitsSet
    have : {x : v.adicCompletion K | ‖x‖ ≤ R} = Metric.closedBall 0 R := by ext x; simp
    rw [this]; exact isCompact_closedBall 0 R
  · have hdet' : ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ = 1 := (norm_eq_one_iff_valued K v _).mpr hdet
    obtain ⟨h1, h2⟩ := hb g hg hdet'
    exact ⟨fun i j => h1 i j, fun i j => h2 i j⟩

include hreg hns in

theorem measure_torusUnits_pos_and_lt_top
    (νT : @Measure (GL (Fin 2) (v.adicCompletion K)) (AutomorphicForm.localGLBorel K v))
    (hνT : ∃ τ₀ : @Measure (AutomorphicForm.localCentralizer K v γ₀) (AutomorphicForm.localCentralizerBorel K v γ₀),
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) τ₀ ∧
      @Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) (AutomorphicForm.localGLBorel K v)
        Subtype.val τ₀ = νT) :
    letI := AutomorphicForm.localGLBorel K v
    0 < νT {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1} ∧
    νT {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1} < ⊤ := by
  letI iG : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := AutomorphicForm.localGLBorel K v
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion K)) := AutomorphicForm.borelSpace_localGLBorel K v
  letI iT : MeasurableSpace (localCentralizer K v γ₀) := AutomorphicForm.localCentralizerBorel K v γ₀
  haveI : BorelSpace (localCentralizer K v γ₀) := @BorelSpace.mk _ _ (localCentralizerBorel K v γ₀) rfl
  obtain ⟨τ₀, hτ₀, hmap⟩ := hνT
  haveI := hτ₀
  set S := {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1} with hS
  have hval : Measurable (Subtype.val : localCentralizer K v γ₀ → GL (Fin 2) (v.adicCompletion K)) :=
    continuous_subtype_val.measurable
  constructor
  ·
    let O : Set (GL (Fin 2) (v.adicCompletion K)) :=
      {g | ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det - 1‖ < 1 ∧
           ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace - 2‖ < 1}
    have hOo : IsOpen O := by
      have hc : Continuous fun g : GL (Fin 2) (v.adicCompletion K) => (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
        Units.continuous_val
      refine IsOpen.inter ?_ ?_
      · exact isOpen_lt (continuous_norm.comp ((hc.matrix_det).sub continuous_const)) continuous_const
      · exact isOpen_lt (continuous_norm.comp ((hc.matrix_trace).sub continuous_const)) continuous_const
    have hOS : (Subtype.val ⁻¹' O : Set (localCentralizer K v γ₀)) ⊆ Subtype.val ⁻¹' S := by
      rintro ⟨g, hg⟩ ⟨h1, h2⟩
      refine ⟨hg, ?_, ?_⟩
      · exact (norm_eq_one_iff_valued K v _).mp (norm_eq_one_of_norm_sub_one_lt K v _ h1)
      · rw [← Valued.toNormedField.norm_le_one_iff]
        calc ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace‖
            = ‖((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace - 2) + 2‖ := by rw [sub_add_cancel]
          _ ≤ max ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace - 2‖ ‖(2 : v.adicCompletion K)‖ :=
              IsUltrametricDist.norm_add_le_max _ _
          _ ≤ 1 := max_le h2.le (norm_two_le_one K v)
    have h1O : (1 : localCentralizer K v γ₀) ∈ (Subtype.val ⁻¹' O : Set (localCentralizer K v γ₀)) := by
      show ((1 : localCentralizer K v γ₀) : GL (Fin 2) (v.adicCompletion K)) ∈ O
      rw [OneMemClass.coe_one]
      refine ⟨?_, ?_⟩
      · show ‖((1 : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det - 1‖ < 1
        rw [Units.val_one, Matrix.det_one, sub_self, norm_zero]; exact one_pos
      · show ‖((1 : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace - 2‖ < 1
        rw [Units.val_one, Matrix.trace_one, Fintype.card_fin]
        norm_num
    have hpos : 0 < τ₀ (Subtype.val ⁻¹' S) :=
      lt_of_lt_of_le ((hOo.preimage continuous_subtype_val).measure_pos τ₀ ⟨1, h1O⟩) (measure_mono hOS)
    calc (0 : ENNReal) < τ₀ (Subtype.val ⁻¹' S) := hpos
      _ ≤ νT S := by rw [← hmap]; exact Measure.le_map_apply hval.aemeasurable S
  ·
    obtain ⟨C, hCc, hSC⟩ := exists_isCompact_superset K v γ₀ hreg hns
    have hSC' : S ⊆ C := fun g hg => hSC g hg.1 hg.2.1
    have hemb : IsClosedEmbedding (Subtype.val : localCentralizer K v γ₀ → GL (Fin 2) (v.adicCompletion K)) :=
      (isClosed_localCentralizer K v γ₀).isClosedEmbedding_subtypeVal
    calc νT S ≤ νT C := measure_mono hSC'
      _ = τ₀ (Subtype.val ⁻¹' C) := by rw [← hmap, Measure.map_apply hval hCc.isClosed.measurableSet]
      _ < ⊤ := (hemb.isCompact_preimage hCc).measure_lt_top

end MeasureA

end Ws31.Torus

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ₀ : GL (Fin 2) (v.adicCompletion K)) (_hreg : AutomorphicForm.IsRegularSemisimple γ₀)
    (_hns : ∀ g : GL (Fin 2) (v.adicCompletion K),
      ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
         ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0))
    (νT : @Measure (GL (Fin 2) (v.adicCompletion K)) (AutomorphicForm.localGLBorel K v))
    (_hνT : ∃ τ₀ : @Measure (AutomorphicForm.localCentralizer K v γ₀) (AutomorphicForm.localCentralizerBorel K v γ₀),
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) τ₀ ∧
      @Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) (AutomorphicForm.localGLBorel K v)
        Subtype.val τ₀ = νT) :
    letI := AutomorphicForm.localGLBorel K v
    0 < νT {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1} ∧
    νT {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1} < ⊤ :=
  Ws31.Torus.measure_torusUnits_pos_and_lt_top K v γ₀ _hreg _hns νT _hνT

end S_AutomorphicForm_measure_setOf_mem_localCentralizer_pos_and_lt_top_of_forall_not_diagonal
end P2MW
export P2MW.S_AutomorphicForm_measure_setOf_mem_localCentralizer_pos_and_lt_top_of_forall_not_diagonal (solution)
