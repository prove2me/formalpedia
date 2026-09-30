-- Prove2me | solution 1 for AccelPPM.FPR.proposition4_1_methods_coincide
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:02:42.841991+00:00
-- url     : https://prove2.me/submissions/f992283b-977a-43cd-be58-c8629510c41b

import Definitions.Def_AccelPPM_FPR_IsMaximalMonotone
import Definitions.Def_AccelPPM_FPR_IsGeneralPPMSeq
import Definitions.Def_AccelPPM_FPR_IsAccelPPMSeq
import Definitions.Def_AccelPPM_FPR_kimCoeff
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic
open scoped BigOperators RealInnerProductSpace
open Finset AccelPPM.FPR
namespace PPMProof
private lemma kim_row {E : Type*} [AddCommGroup E] [Module ℝ E] (v : ℕ → E)
    (i : ℕ) (hi : 1 ≤ i) :
    (∑ k ∈ range i, kimCoeff i (k+1) • v (k+1)) =
      (2*(i : ℝ)/((i : ℝ)+1)) • v i -
      (2/((i : ℝ)*((i : ℝ)+1))) • (∑ k ∈ range (i-1), (k+1 : ℝ) • v (k+1)) := by
  have he : i = (i-1)+1 := by omega
  conv_lhs => rw [he]
  rw [sum_range_succ]
  simp only [Nat.sub_add_cancel hi]
  have hs : ∀ k ∈ range (i-1), kimCoeff i (k+1) = -(2/((i : ℝ)*((i : ℝ)+1)))*(k+1 : ℝ) := by
    intro k hk
    have hki : k+1 ≠ i := by have := mem_range.mp hk; omega
    simp only [kimCoeff, if_neg hki, Nat.cast_add, Nat.cast_one]
    ring
  have hS : (∑ k ∈ range (i-1), kimCoeff i (k+1) • v (k+1)) =
      -(2/((i : ℝ)*((i : ℝ)+1))) • (∑ k ∈ range (i-1), (k+1 : ℝ) • v (k+1)) := by
    rw [smul_sum]
    apply sum_congr rfl
    intro k hk
    rw [hs k hk, mul_smul]
  rw [hS]
  simp [kimCoeff]
  module
private lemma cumulative_kim {E : Type*} [AddCommGroup E] [Module ℝ E] (v : ℕ → E) (i : ℕ) :
    (∑ j ∈ range i, ∑ k ∈ range (j+1), kimCoeff (j+1) (k+1) • v (k+1)) =
      (2/((i : ℝ)+1)) • (∑ k ∈ range i, (k+1 : ℝ) • v (k+1)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [sum_range_succ, ih, kim_row v (i+1) (by omega)]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, sum_range_succ]
    have hi1 : (i : ℝ)+1 ≠ 0 := by positivity
    have hi2 : (i : ℝ)+1+1 ≠ 0 := by positivity
    match_scalars <;> field_simp <;> ring
private lemma resolvent_unique {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : H → Set H) (hM : IsMonotoneOp M) (lam : ℝ) (hlam : 0 < lam)
    (y x z : H) (hx : lam⁻¹ • (y-x) ∈ M x) (hz : lam⁻¹ • (y-z) ∈ M z) : x = z := by
  have hh := hM x z _ _ hx hz
  have he : lam⁻¹ • (y-x) - lam⁻¹ • (y-z) = -lam⁻¹ • (x-z) := by module
  rw [he, inner_smul_right, real_inner_self_eq_norm_sq] at hh
  have hl : 0 < lam⁻¹ := inv_pos.mpr hlam
  have hsq : ‖x-z‖^2 ≤ 0 := le_of_not_gt (fun hs => (not_lt_of_ge hh) (by nlinarith [mul_pos hl hs]))
  have hn : ‖x-z‖ = 0 := by nlinarith [norm_nonneg (x-z)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)
private lemma general_prefix {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : H → Set H) (lam : ℝ) (x y : ℕ → H) (h : IsGeneralPPMSeq M lam kimCoeff x y) (i : ℕ) :
    y i = y 0 + (2/((i : ℝ)+1)) • (∑ k ∈ range i, (k+1 : ℝ) • (x (k+1)-y k)) := by
  have he : ∀ i, y i = y 0 + ∑ j ∈ range i, ∑ k ∈ range (j+1), kimCoeff (j+1) (k+1) • (x (k+1)-y k) := by
    intro i; induction i with
    | zero => simp
    | succ i ih =>
      rw [h.2 i, ih, add_assoc]
      congr 1
      exact (sum_range_succ _ _).symm
  rw [he i]
  congr 1
  convert cumulative_kim (fun k => x k-y (k-1)) i using 1 <;> simp
private lemma general_halpern {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : H → Set H) (lam : ℝ) (x y : ℕ → H) (h : IsGeneralPPMSeq M lam kimCoeff x y) (i : ℕ) :
    y (i+1) = (1/((i : ℝ)+2)) • y 0 + (((i : ℝ)+1)/((i : ℝ)+2)) • (2 • x (i+1)-y i) := by
  rw [general_prefix M lam x y h (i+1), sum_range_succ]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [general_prefix M lam x y h i]
  have hi1 : (i : ℝ)+1 ≠ 0 := by positivity
  have hi2 : (i : ℝ)+2 ≠ 0 := by positivity
  match_scalars <;> field_simp <;> ring
private lemma accel_identity {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : H → Set H) (lam : ℝ) (x y : ℕ → H) (h : IsAccelPPMSeq M lam x y) (i : ℕ) :
    ((i : ℝ)+1) • y i + (i : ℝ) • y (i-1) - (2*(i : ℝ)) • x i = y 0 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [h.2.2 i, ← ih]
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    have hi2 : (i : ℝ)+2 ≠ 0 := by positivity
    match_scalars <;> field_simp <;> ring
private lemma accel_halpern {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : H → Set H) (lam : ℝ) (x y : ℕ → H) (h : IsAccelPPMSeq M lam x y) (i : ℕ) :
    y (i+1) = (1/((i : ℝ)+2)) • y 0 + (((i : ℝ)+1)/((i : ℝ)+2)) • (2 • x (i+1)-y i) := by
  rw [h.2.2 i, ← accel_identity M lam x y h i]
  have hi2 : (i : ℝ)+2 ≠ 0 := by positivity
  match_scalars <;> field_simp <;> ring
private theorem methods_coincide {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : H → Set H) (hM : IsMaximalMonotone M) (lam : ℝ) (hlam : 0 < lam)
    (x' y' : ℕ → H) (hgen : IsGeneralPPMSeq M lam kimCoeff x' y')
    (x y : ℕ → H) (hacc : IsAccelPPMSeq M lam x y) (h0 : y' 0 = y 0) :
    (∀ i, 1 ≤ i → x' i = x i) ∧ ∀ i, y' i = y i := by
  have hy : ∀ i, y' i = y i := by
    intro i; induction i with
    | zero => exact h0
    | succ i ih =>
      have hx : x' (i+1) = x (i+1) := resolvent_unique M hM.1 lam hlam (y i) _ _
        (by simpa only [ih] using hgen.1 i) (hacc.2.1 i)
      rw [general_halpern M lam x' y' hgen i, accel_halpern M lam x y hacc i, h0, ih, hx]
  refine ⟨?_, hy⟩
  intro i hi
  have hx := resolvent_unique M hM.1 lam hlam (y (i-1)) (x' i) (x i)
    (by simpa only [Nat.sub_add_cancel hi, hy] using hgen.1 (i-1))
    (by simpa only [Nat.sub_add_cancel hi] using hacc.2.1 (i-1))
  exact hx

end PPMProof

 theorem solution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (M : H → Set H) (hM : IsMaximalMonotone M) (lam : ℝ) (hlam : 0 < lam)
    (x' y' : ℕ → H) (hgen : IsGeneralPPMSeq M lam kimCoeff x' y')
    (x y : ℕ → H) (hacc : IsAccelPPMSeq M lam x y) (h0 : y' 0 = y 0) :
    (∀ i : ℕ, 1 ≤ i → x' i = x i) ∧ ∀ i : ℕ, y' i = y i := by
  exact PPMProof.methods_coincide M hM lam hlam x' y' hgen x y hacc h0
