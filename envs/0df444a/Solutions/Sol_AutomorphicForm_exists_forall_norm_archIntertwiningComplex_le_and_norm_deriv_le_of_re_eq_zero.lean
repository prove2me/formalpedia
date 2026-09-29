-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_archIntertwiningComplex_le_and_norm_deriv_le_of_re_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/f7476d75-9894-5e4b-bbb9-107206cef496

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_norm_archIntertwiningComplex_le_and_norm_deriv_le_of_re_eq_zero

set_option autoImplicit false

namespace Ws31
namespace AxisC

open Complex Finset

theorem Gamma_mul_inv_Gamma_add (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    Complex.Gamma z * (Complex.Gamma (z + (n : ℂ)))⁻¹ = ∏ i ∈ Finset.range n, (z + (i : ℂ))⁻¹ := by
  have hzne : ∀ i : ℕ, z + (i : ℂ) ≠ 0 := by
    intro i h; have := congrArg Complex.re h; simp at this; have : (0:ℝ) ≤ i := Nat.cast_nonneg i; linarith
  have hGne : ∀ i : ℕ, Complex.Gamma (z + (i : ℂ)) ≠ 0 := fun i =>
    Complex.Gamma_ne_zero fun m h => by
      have := congrArg Complex.re h; simp at this
      have : (0:ℝ) ≤ i := Nat.cast_nonneg i; have : (0:ℝ) ≤ m := Nat.cast_nonneg m; linarith
  induction n with
  | zero => have h0 := hGne 0; simp only [Nat.cast_zero, add_zero] at h0; simp [mul_inv_cancel₀ h0]
  | succ n ih =>
    rw [Finset.prod_range_succ, ← ih, show z + ((n + 1 : ℕ) : ℂ) = (z + (n : ℂ)) + 1 by push_cast; ring,
      Complex.Gamma_add_one _ (hzne n)]
    have := hGne n
    field_simp

theorem inv_linear_axis (W : ℂ) (hW : W.re = 0) (b : ℝ) (hb : (1 / 2 : ℝ) ≤ b) :
    W + (b : ℂ) ≠ 0 ∧ (b : ℝ) ≤ ‖W + (b : ℂ)‖ ∧ ‖(W + (b : ℂ))⁻¹‖ ≤ 2 ∧
      HasDerivAt (fun z : ℂ => (z + (b : ℂ))⁻¹) (-((W + (b : ℂ)) ^ 2)⁻¹) W ∧ ‖-((W + (b : ℂ)) ^ 2)⁻¹‖ ≤ 4 := by
  have hre : (W + (b : ℂ)).re = b := by simp [hW]
  have hnorm : (b : ℝ) ≤ ‖W + (b : ℂ)‖ := by
    have := Complex.abs_re_le_norm (W + (b : ℂ)); rw [hre, abs_of_nonneg (by linarith)] at this; exact this
  have hne : W + (b : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hnorm; linarith
  have hinv : ‖(W + (b : ℂ))⁻¹‖ ≤ 2 := by
    rw [norm_inv]; exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
  refine ⟨hne, hnorm, hinv, ?_, ?_⟩
  · have h := ((hasDerivAt_id W).add_const (b : ℂ)).inv hne
    have h' : HasDerivAt (fun z : ℂ => (z + (b : ℂ))⁻¹) (-(1 : ℂ) / (W + (b : ℂ)) ^ 2) W := by
      convert h using 1
      rfl
      rfl
      rfl
      rfl
    convert h' using 1
    rw [neg_div, one_div]
  · rw [norm_neg, norm_inv, norm_pow]
    have : (1 / 2 : ℝ) ^ 2 ≤ ‖W + (b : ℂ)‖ ^ 2 := by gcongr; linarith
    calc (‖W + (b : ℂ)‖ ^ 2)⁻¹ ≤ ((1 / 2 : ℝ) ^ 2)⁻¹ := inv_anti₀ (by norm_num) this
      _ = 4 := by norm_num

theorem prod_inv_linear_axis (W : ℂ) (hW : W.re = 0) (n : ℕ) (b : ℕ → ℝ) (hb : ∀ i, (1 / 2 : ℝ) ≤ b i) :
    ‖∏ i ∈ Finset.range n, (W + (b i : ℂ))⁻¹‖ ≤ 2 ^ n ∧
    HasDerivAt (fun z : ℂ => ∏ i ∈ Finset.range n, (z + (b i : ℂ))⁻¹)
      (∑ i ∈ Finset.range n, (∏ l ∈ (Finset.range n).erase i, (W + (b l : ℂ))⁻¹) • (-((W + (b i : ℂ)) ^ 2)⁻¹)) W ∧
    ‖∑ i ∈ Finset.range n, (∏ l ∈ (Finset.range n).erase i, (W + (b l : ℂ))⁻¹) • (-((W + (b i : ℂ)) ^ 2)⁻¹)‖
      ≤ n * (4 * 2 ^ n) := by
  have hprodle : ∀ s : Finset ℕ, ‖∏ l ∈ s, (W + (b l : ℂ))⁻¹‖ ≤ 2 ^ s.card := by
    intro s
    rw [norm_prod]
    calc ∏ l ∈ s, ‖(W + (b l : ℂ))⁻¹‖ ≤ ∏ l ∈ s, (2 : ℝ) :=
          Finset.prod_le_prod (fun l _ => norm_nonneg _) fun l _ => (inv_linear_axis W hW (b l) (hb l)).2.2.1
      _ = 2 ^ s.card := by rw [Finset.prod_const]
  refine ⟨by simpa using hprodle (Finset.range n), ?_, ?_⟩
  · have h := HasDerivAt.finsetProd (u := Finset.range n) (f := fun i z => (z + (b i : ℂ))⁻¹)
      (f' := fun i => -((W + (b i : ℂ)) ^ 2)⁻¹) (x := W) fun i _ => (inv_linear_axis W hW (b i) (hb i)).2.2.2.1
    convert h using 2
    · rfl
    · rfl
    simp only [Finset.prod_apply]
  · refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i ∈ Finset.range n,
        ‖(∏ l ∈ (Finset.range n).erase i, (W + (b l : ℂ))⁻¹) • (-((W + (b i : ℂ)) ^ 2)⁻¹)‖ ≤ 4 * 2 ^ n := by
      intro i hi
      rw [smul_eq_mul, norm_mul]
      have h1 := hprodle ((Finset.range n).erase i)
      have hcard : ((Finset.range n).erase i).card ≤ n := (Finset.card_erase_le).trans (by simp)
      have h1' : ‖∏ l ∈ (Finset.range n).erase i, (W + (b l : ℂ))⁻¹‖ ≤ 2 ^ n :=
        h1.trans (pow_le_pow_right₀ (by norm_num) hcard)
      have h2 := (inv_linear_axis W hW (b i) (hb i)).2.2.2.2
      calc _ ≤ 2 ^ n * 4 := mul_le_mul h1' h2 (norm_nonneg _) (by positivity)
        _ = 4 * 2 ^ n := by ring
    calc ∑ i ∈ Finset.range n, ‖(∏ l ∈ (Finset.range n).erase i, (W + (b l : ℂ))⁻¹) • (-((W + (b i : ℂ)) ^ 2)⁻¹)‖
        ≤ ∑ i ∈ Finset.range n, (4 * 2 ^ n : ℝ) := Finset.sum_le_sum hterm
      _ = n * (4 * 2 ^ n) := by rw [Finset.sum_const, Finset.card_range]; simp

theorem ratio_axis (W : ℂ) (hW : W.re = 0) (M : ℕ) (b : ℝ) (hb : (1 / 2 : ℝ) ≤ b) :
    ‖(W + (M : ℂ) / 2) * (W + (b : ℂ))⁻¹‖ ≤ 2 + M ∧
    HasDerivAt (fun z : ℂ => (z + (M : ℂ) / 2) * (z + (b : ℂ))⁻¹)
      ((W + (b : ℂ))⁻¹ + (W + (M : ℂ) / 2) * (-((W + (b : ℂ)) ^ 2)⁻¹)) W ∧
    ‖(W + (b : ℂ))⁻¹ + (W + (M : ℂ) / 2) * (-((W + (b : ℂ)) ^ 2)⁻¹)‖ ≤ 2 + (4 + 2 * M) := by
  obtain ⟨hne, hnorm, hinv, hder, hder'⟩ := inv_linear_axis W hW b hb
  have hb0 : 0 < b := by linarith
  have hinvb : ‖(W + (b : ℂ))⁻¹‖ ≤ b⁻¹ := by rw [norm_inv]; exact inv_anti₀ hb0 hnorm

  have hsplit : (W + (M : ℂ) / 2) * (W + (b : ℂ))⁻¹ = 1 + (((M : ℝ) / 2 - b : ℝ) : ℂ) * (W + (b : ℂ))⁻¹ := by
    have : (W + (M : ℂ) / 2) = (W + (b : ℂ)) + (((M : ℝ) / 2 - b : ℝ) : ℂ) := by push_cast; ring
    rw [this, add_mul, mul_inv_cancel₀ hne]
  have hc : ‖(((M : ℝ) / 2 - b : ℝ) : ℂ)‖ ≤ (M : ℝ) / 2 + b := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact (abs_sub _ _).trans (by rw [abs_of_nonneg (by positivity), abs_of_pos hb0])
  have hMb : ((M : ℝ) / 2 + b) * b⁻¹ ≤ 1 + M := by
    rw [add_mul, mul_inv_cancel₀ hb0.ne']
    have : (M : ℝ) / 2 * b⁻¹ ≤ M := by
      rw [div_mul_eq_mul_div, mul_comm]
      have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      calc b⁻¹ * (M : ℝ) / 2 ≤ 2 * (M : ℝ) / 2 := by gcongr; exact inv_le_of_inv_le₀ (by norm_num) (by rw [show (2:ℝ)⁻¹ = 1 / 2 by norm_num]; exact hb)
        _ = M := by ring
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_mul]
    have := mul_le_mul hc hinvb (norm_nonneg _) (by positivity)
    linarith
  · exact ((hasDerivAt_id W).add_const ((M : ℂ) / 2)).mul hder |>.congr_deriv (by simp)
  · refine (norm_add_le _ _).trans (add_le_add hinv ?_)

    have heq : (W + (M : ℂ) / 2) * (-((W + (b : ℂ)) ^ 2)⁻¹) = -(((W + (M : ℂ) / 2) * (W + (b : ℂ))⁻¹) * (W + (b : ℂ))⁻¹) := by
      field_simp
    rw [heq, norm_neg, norm_mul]
    have h1 : ‖(W + (M : ℂ) / 2) * (W + (b : ℂ))⁻¹‖ ≤ 2 + M := by
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      rw [norm_one, norm_mul]
      have := mul_le_mul hc hinvb (norm_nonneg _) (by positivity)
      linarith
    have := mul_le_mul h1 hinv (norm_nonneg _) (by positivity)
    linarith

theorem main (a m M : ℕ) (hm : 2 * a ≤ m) (hM : m = 2 * a → M = 0) :
    let N : ℂ → ℂ := fun W => ((a.factorial : ℕ) : ℂ) / 2 *
      (if m = 2 * a ∧ M = 0 then
        Complex.Gamma (W + 1) * (Complex.Gamma (W + 1 + (a : ℂ)))⁻¹
      else
        (W + (M : ℂ) / 2) * Complex.Gamma (W + (m : ℂ) / 2 - (a : ℂ)) * (Complex.Gamma (W + (m : ℂ) / 2 + 1))⁻¹)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℂ, W.re = 0 → ‖N W‖ ≤ C ∧ DifferentiableAt ℂ N W ∧ ‖deriv N W‖ ≤ C := by
  intro N
  set K₀ : ℝ := (a.factorial : ℝ) / 2 with hK₀
  have hK : ‖(((a.factorial : ℕ) : ℂ) / 2)‖ = K₀ := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_two]
  have hK0 : 0 ≤ K₀ := by positivity

  refine ⟨K₀ * 2 ^ a * (2 + M) * (4 * a + 4), by positivity, fun W hW => ?_⟩
  have h2a : (1 : ℝ) ≤ 2 ^ a := one_le_pow₀ (by norm_num)
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  by_cases hcase : m = 2 * a ∧ M = 0
  ·
    set b : ℕ → ℝ := fun i => 1 + i with hb
    have hb' : ∀ i, (1 / 2 : ℝ) ≤ b i := fun i => by simp only [hb]; have : (0:ℝ) ≤ i := Nat.cast_nonneg i; linarith
    have hform : ∀ z : ℂ, -(1 / 2 : ℝ) < z.re → N z = ((a.factorial : ℕ) : ℂ) / 2 * ∏ i ∈ Finset.range a, (z + (b i : ℂ))⁻¹ := by
      intro z hz
      simp only [N, if_pos hcase]
      rw [show z + 1 + (a : ℂ) = (z + 1) + (a : ℂ) by ring, Gamma_mul_inv_Gamma_add (z + 1) (by simp; linarith) a]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [hb]; push_cast; ring
    obtain ⟨hP, hPd, hPd'⟩ := prod_inv_linear_axis W hW a b hb'
    have hev : N =ᶠ[nhds W] fun z => ((a.factorial : ℕ) : ℂ) / 2 * ∏ i ∈ Finset.range a, (z + (b i : ℂ))⁻¹ := by
      have hopen : IsOpen {z : ℂ | -(1 / 2 : ℝ) < z.re} := isOpen_lt continuous_const Complex.continuous_re
      exact Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, hopen.mem_nhds (by simp [hW]), fun z hz => hform z hz⟩
    have hNd : HasDerivAt N _ W := (hPd.const_mul (((a.factorial : ℕ) : ℂ) / 2)).congr_of_eventuallyEq hev
    refine ⟨?_, hNd.differentiableAt, ?_⟩
    · rw [hform W (by rw [hW]; norm_num), norm_mul, hK]
      have hY : (1 : ℝ) ≤ (2 + M) * (4 * a + 4) := by nlinarith
      calc K₀ * ‖∏ i ∈ Finset.range a, (W + (b i : ℂ))⁻¹‖ ≤ K₀ * 2 ^ a := mul_le_mul_of_nonneg_left hP hK0
        _ = K₀ * 2 ^ a * 1 := by ring
        _ ≤ K₀ * 2 ^ a * ((2 + M) * (4 * a + 4)) := mul_le_mul_of_nonneg_left hY (mul_nonneg hK0 (by positivity))
        _ = K₀ * 2 ^ a * (2 + M) * (4 * a + 4) := by ring
    · rw [hNd.deriv, norm_mul, hK]
      have hY : (4 : ℝ) * a ≤ (2 + M) * (4 * a + 4) := by nlinarith
      calc K₀ * ‖∑ i ∈ Finset.range a, (∏ l ∈ (Finset.range a).erase i, (W + (b l : ℂ))⁻¹) • (-((W + (b i : ℂ)) ^ 2)⁻¹)‖
          ≤ K₀ * (a * (4 * 2 ^ a)) := mul_le_mul_of_nonneg_left hPd' hK0
        _ = K₀ * 2 ^ a * (4 * a) := by ring
        _ ≤ K₀ * 2 ^ a * ((2 + M) * (4 * a + 4)) := mul_le_mul_of_nonneg_left hY (mul_nonneg hK0 (by positivity))
        _ = K₀ * 2 ^ a * (2 + M) * (4 * a + 4) := by ring
  ·
    have hne2a : m ≠ 2 * a := fun h => hcase ⟨h, hM h⟩
    have hm1 : 2 * a + 1 ≤ m := by omega
    have hm1R : (2 * a + 1 : ℝ) ≤ m := by exact_mod_cast hm1
    set b : ℕ → ℝ := fun i => (m : ℝ) / 2 - a + i with hb
    have hb' : ∀ i, (1 / 2 : ℝ) ≤ b i := fun i => by simp only [hb]; have : (0:ℝ) ≤ i := Nat.cast_nonneg i; linarith
    have hform : ∀ z : ℂ, -(1 / 4 : ℝ) < z.re → N z = ((a.factorial : ℕ) : ℂ) / 2 *
        (((z + (M : ℂ) / 2) * (z + (b 0 : ℂ))⁻¹) * ∏ i ∈ Finset.range a, (z + (b (i + 1) : ℂ))⁻¹) := by
      intro z hz
      simp only [N, if_neg hcase]
      have hz' : 0 < (z + (m : ℂ) / 2 - (a : ℂ)).re := by simp; linarith
      rw [show z + (m : ℂ) / 2 + 1 = (z + (m : ℂ) / 2 - (a : ℂ)) + ((a + 1 : ℕ) : ℂ) by push_cast; ring, mul_assoc,
        Gamma_mul_inv_Gamma_add _ hz' (a + 1), Finset.prod_range_succ']
      congr 1
      rw [mul_comm (∏ i ∈ Finset.range a, _), mul_assoc]
      have e0 : W = W := rfl
      have hb0 : (z + (m : ℂ) / 2 - (a : ℂ) + ((0 : ℕ) : ℂ))⁻¹ = (z + (b 0 : ℂ))⁻¹ := by
        simp only [hb]; push_cast; ring_nf
      have hbi : ∏ i ∈ Finset.range a, (z + (m : ℂ) / 2 - (a : ℂ) + ((i + 1 : ℕ) : ℂ))⁻¹ =
          ∏ i ∈ Finset.range a, (z + (b (i + 1) : ℂ))⁻¹ :=
        Finset.prod_congr rfl fun i _ => by simp only [hb]; push_cast; ring_nf
      rw [hb0, hbi]
    obtain ⟨hP, hPd, hPd'⟩ := prod_inv_linear_axis W hW a (fun i => b (i + 1)) (fun i => hb' (i + 1))
    obtain ⟨hg, hgd, hgd'⟩ := ratio_axis W hW M (b 0) (hb' 0)
    have hev : N =ᶠ[nhds W] fun z => ((a.factorial : ℕ) : ℂ) / 2 *
        (((z + (M : ℂ) / 2) * (z + (b 0 : ℂ))⁻¹) * ∏ i ∈ Finset.range a, (z + (b (i + 1) : ℂ))⁻¹) := by
      have hopen : IsOpen {z : ℂ | -(1 / 4 : ℝ) < z.re} := isOpen_lt continuous_const Complex.continuous_re
      exact Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, hopen.mem_nhds (by simp [hW]), fun z hz => hform z hz⟩
    have hNd : HasDerivAt N _ W := ((hgd.mul hPd).const_mul (((a.factorial : ℕ) : ℂ) / 2)).congr_of_eventuallyEq hev
    refine ⟨?_, hNd.differentiableAt, ?_⟩
    · rw [hform W (by rw [hW]; norm_num), norm_mul, hK, norm_mul]
      have hY : (2 : ℝ) + M ≤ (2 + M) * (4 * a + 4) := by nlinarith
      calc K₀ * (‖(W + (M : ℂ) / 2) * (W + (b 0 : ℂ))⁻¹‖ * ‖∏ i ∈ Finset.range a, (W + (b (i + 1) : ℂ))⁻¹‖)
          ≤ K₀ * ((2 + M) * 2 ^ a) := mul_le_mul_of_nonneg_left (mul_le_mul hg hP (norm_nonneg _) (by positivity)) hK0
        _ = K₀ * 2 ^ a * (2 + M) := by ring
        _ ≤ K₀ * 2 ^ a * ((2 + M) * (4 * a + 4)) := mul_le_mul_of_nonneg_left hY (mul_nonneg hK0 (by positivity))
        _ = K₀ * 2 ^ a * (2 + M) * (4 * a + 4) := by ring
    · rw [hNd.deriv, norm_mul, hK]
      have h1 : ‖((W + (b 0 : ℂ))⁻¹ + (W + (M : ℂ) / 2) * (-((W + (b 0 : ℂ)) ^ 2)⁻¹)) *
            ∏ i ∈ Finset.range a, (W + (b (i + 1) : ℂ))⁻¹‖ ≤ (2 + (4 + 2 * M)) * 2 ^ a := by
        rw [norm_mul]; exact mul_le_mul hgd' hP (norm_nonneg _) (by positivity)
      have h2 : ‖((W + (M : ℂ) / 2) * (W + (b 0 : ℂ))⁻¹) *
            ∑ i ∈ Finset.range a, (∏ l ∈ (Finset.range a).erase i, (W + (b (l + 1) : ℂ))⁻¹) • (-((W + (b (i + 1) : ℂ)) ^ 2)⁻¹)‖
            ≤ (2 + M) * (a * (4 * 2 ^ a)) := by
        rw [norm_mul]; exact mul_le_mul hg hPd' (norm_nonneg _) (by positivity)
      calc K₀ * ‖((W + (b 0 : ℂ))⁻¹ + (W + (M : ℂ) / 2) * (-((W + (b 0 : ℂ)) ^ 2)⁻¹)) *
              ∏ i ∈ Finset.range a, (W + (b (i + 1) : ℂ))⁻¹ +
            ((W + (M : ℂ) / 2) * (W + (b 0 : ℂ))⁻¹) *
              ∑ i ∈ Finset.range a, (∏ l ∈ (Finset.range a).erase i, (W + (b (l + 1) : ℂ))⁻¹) • (-((W + (b (i + 1) : ℂ)) ^ 2)⁻¹)‖
          ≤ K₀ * ((2 + (4 + 2 * M)) * 2 ^ a + (2 + M) * (a * (4 * 2 ^ a))) :=
            mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add h1 h2)) hK0
        _ = K₀ * 2 ^ a * ((6 + 2 * M) + (2 + M) * (4 * a)) := by ring
        _ ≤ K₀ * 2 ^ a * ((2 + M) * (4 * a + 4)) :=
            mul_le_mul_of_nonneg_left (by nlinarith) (mul_nonneg hK0 (by positivity))
        _ = K₀ * 2 ^ a * (2 + M) * (4 * a + 4) := by ring

end Ws31.AxisC

theorem solution (a m M : ℕ) (hm : 2 * a ≤ m) (hM : m = 2 * a → M = 0) :
    let N : ℂ → ℂ := fun W => ((a.factorial : ℕ) : ℂ) / 2 *
      (if m = 2 * a ∧ M = 0 then
        Complex.Gamma (W + 1) * (Complex.Gamma (W + 1 + (a : ℂ)))⁻¹
      else
        (W + (M : ℂ) / 2) * Complex.Gamma (W + (m : ℂ) / 2 - (a : ℂ)) * (Complex.Gamma (W + (m : ℂ) / 2 + 1))⁻¹)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℂ, W.re = 0 → ‖N W‖ ≤ C ∧ DifferentiableAt ℂ N W ∧ ‖deriv N W‖ ≤ C :=
  Ws31.AxisC.main a m M hm hM

end S_AutomorphicForm_exists_forall_norm_archIntertwiningComplex_le_and_norm_deriv_le_of_re_eq_zero
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_archIntertwiningComplex_le_and_norm_deriv_le_of_re_eq_zero (solution)
