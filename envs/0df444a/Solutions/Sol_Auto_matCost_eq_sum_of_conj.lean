-- Prove2me | solution 1 for Auto.matCost_eq_sum_of_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:08:21.641715+00:00
-- url     : https://prove2.me/submissions/ef162914-6653-4e43-ac1a-3ac5d9e6fbdb

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_P2M_Auto_ofReal_sum_le__f3920bf70ced
public import Theorems.Thm_Auto_costInt_conj
public import Theorems.Thm_Auto_ofReal_costTerm_le

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
namespace Auto
theorem _root_.solution {P : Matrix n n ℂ} (U : Matrix.unitaryGroup n ℂ) (p : n → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hPU : P = (U : Matrix n n ℂ) * diagonal (fun i => ((p i : ℝ) : ℂ)) * star (U : Matrix n n
      ℂ)) (K : Matrix n n ℂ) :
    matCost P K = ∑ i, ∑ j, ENNReal.ofReal ((3 / 2) * ‖(star (U : Matrix n n ℂ) * K * (U :
      Matrix n n ℂ)) i j‖ ^ 2) / ENNReal.ofReal (√(p i) + √(p j)) := by
  classical
  have hA : CFC.sqrt P = (U : Matrix n n ℂ) * diagonal (fun i => ((√(p i) : ℝ) : ℂ)) *
      star (U : Matrix n n ℂ) := by
    have hD : (diagonal (fun i => ((√(p i) : ℝ) : ℂ))).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]; intro i; exact_mod_cast Real.sqrt_nonneg _
    have hnn : 0 ≤ (U : Matrix n n ℂ) * diagonal (fun i => ((√(p i) : ℝ) : ℂ)) *
        star (U : Matrix n n ℂ) := by
      have := hD.mul_mul_conjTranspose_same (U : Matrix n n ℂ)
      rw [← Matrix.star_eq_conjTranspose] at this
      exact this.nonneg
    refine CFC.sqrt_unique ?_ hnn
    have hUU : star (U : Matrix n n ℂ) * U = 1 := Unitary.coe_star_mul_self U
    calc (U : Matrix n n ℂ) * diagonal (fun i => ((√(p i) : ℝ) : ℂ)) * star (U : Matrix n n ℂ) * ((U
        : Matrix n n ℂ) * diagonal (fun i => ((√(p i) : ℝ) : ℂ)) * star (U : Matrix n n ℂ))
        = (U : Matrix n n ℂ) * (diagonal (fun i => ((√(p i) : ℝ) : ℂ)) * (star (U : Matrix n n ℂ) *
            U) * diagonal (fun i => ((√(p i) : ℝ) : ℂ))) *
              star (U : Matrix n n ℂ) := by simp only [Matrix.mul_assoc]
      _ = P := by
        rw [hUU, Matrix.mul_one, Matrix.diagonal_mul_diagonal, hPU]
        congr 3; funext i
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hp i)]
  set c : n → n → ℝ := fun i j => √(p i) + √(p j)
  have hc : ∀ i j, 0 ≤ c i j := fun i j => by positivity
  set Kt := star (U : Matrix n n ℂ) * K * U
  have hUU : star (U : Matrix n n ℂ) * U = 1 := Unitary.coe_star_mul_self U
  have hUU' : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 := Unitary.coe_mul_star_self U
  have hconj : ∀ Y : Matrix n n ℂ,
      star (U : Matrix n n ℂ) * ((U : Matrix n n ℂ) * Y * star (U : Matrix n n ℂ)) * U = Y := by
    intro Y
    simp only [Matrix.mul_assoc, hUU, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hUU, Matrix.one_mul]
  apply le_antisymm
  · refine iSup_le fun X => ?_
    rw [costInt_conj U (fun i => √(p i)) hA, Finset.mul_sum]
    refine (ofReal_sum_le' _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [Finset.mul_sum]
    refine (ofReal_sum_le' _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    exact ofReal_costTerm_le _ _ (hc i j)
  · by_cases hinf : ∃ i j, c i j = 0 ∧ Kt i j ≠ 0
    · obtain ⟨i0, j0, hc0, hk0⟩ := hinf
      have htop : matCost P K = ⊤ := by
        refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
        set lam : ℝ := (r : ℝ) / (3 * ‖Kt i0 j0‖ ^ 2) + 1
        set Yt : Matrix n n ℂ := Matrix.of fun i j =>
          if i = i0 ∧ j = j0 then (lam : ℂ) * Kt i0 j0 else 0
        refine le_trans ?_ (le_iSup _ ((U : Matrix n n ℂ) * Yt * star (U : Matrix n n ℂ)))
        rw [costInt_conj U (fun i => √(p i)) hA, hconj]
        have hsum : ∑ i, ∑ j, (2 * ((starRingEnd ℂ) (Kt i j) * Yt i j).re -
            c i j * ‖Yt i j‖ ^ 2) = 2 * lam * ‖Kt i0 j0‖ ^ 2 := by
          rw [Finset.sum_eq_single i0, Finset.sum_eq_single j0]
          · simp only [Yt, Matrix.of_apply, and_self, ite_true, hc0, zero_mul, sub_zero]
            rw [← mul_assoc, mul_comm ((starRingEnd ℂ) (Kt i0 j0)), mul_assoc,
              ← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul,
              Complex.normSq_eq_norm_sq]
            norm_cast; ring
          · intro j _ hj; simp [Yt, hj]
          · simp
          · intro i _ hi
            refine Finset.sum_eq_zero fun j _ => ?_
            simp [Yt, hi]
          · simp
        rw [hsum, ← ENNReal.ofReal_coe_nnreal]
        apply ENNReal.ofReal_le_ofReal
        have hk : 0 < ‖Kt i0 j0‖ ^ 2 := by positivity
        have : (r : ℝ) ≤ 3 * ‖Kt i0 j0‖ ^ 2 * lam := by
          simp only [lam]
          have : 3 * ‖Kt i0 j0‖ ^ 2 * ((r : ℝ) / (3 * ‖Kt i0 j0‖ ^ 2)) = r := by
            field_simp
          rw [mul_add, this]
          nlinarith [NNReal.coe_nonneg r]
        nlinarith
      rw [htop]; exact le_top
    · push Not at hinf
      set Yt : Matrix n n ℂ := Matrix.of fun i j =>
        if c i j = 0 then 0 else Kt i j / (c i j : ℂ)
      refine le_trans ?_ (le_iSup _ ((U : Matrix n n ℂ) * Yt * star (U : Matrix n n ℂ)))
      rw [costInt_conj U (fun i => √(p i)) hA, hconj]
      have hterm : ∀ i j, (3 / 2) * (2 * ((starRingEnd ℂ) (Kt i j) * Yt i j).re -
          c i j * ‖Yt i j‖ ^ 2) = (3 / 2) * ‖Kt i j‖ ^ 2 / c i j := by
        intro i j
        by_cases h0 : c i j = 0
        · simp [Yt, h0, hinf i j h0]
        · have hcpos : 0 < c i j := lt_of_le_of_ne (hc i j) (Ne.symm h0)
          simp only [Yt, Matrix.of_apply, h0, ite_false]
          rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hc i j), div_pow]
          have : ((starRingEnd ℂ) (Kt i j) * (Kt i j / (c i j : ℂ))).re =
              ‖Kt i j‖ ^ 2 / c i j := by
            rw [mul_div_assoc', ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
            rw [show ((‖Kt i j‖ ^ 2 : ℝ) : ℂ) / (c i j : ℂ) = ((‖Kt i j‖ ^ 2 / c i j : ℝ) : ℂ)
              by push_cast; ring]
            rw [Complex.ofReal_re]
          rw [this]
          field_simp
          ring
      have hsum : (3 / 2) * ∑ i, ∑ j, (2 * ((starRingEnd ℂ) (Kt i j) * Yt i j).re -
          c i j * ‖Yt i j‖ ^ 2) = ∑ i, ∑ j, (3 / 2) * ‖Kt i j‖ ^ 2 / c i j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => hterm i j
      rw [hsum]
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => by
        have := hc i j; positivity)]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by have := hc i j; positivity)]
      refine Finset.sum_le_sum fun j _ => ?_
      by_cases h0 : c i j = 0
      · simp [h0, hinf i j h0]
      · have hcpos : 0 < c i j := lt_of_le_of_ne (hc i j) (Ne.symm h0)
        rw [ENNReal.ofReal_div_of_pos hcpos]
end Auto
