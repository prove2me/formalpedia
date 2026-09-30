-- Prove2me | solution 1 for AndersonAccel.Safe.norm_windowB_le
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:49:52.65872+00:00
-- url     : https://prove2.me/submissions/5b33943b-4e30-4087-a306-2489b9efbf58

import Definitions.Def_AndersonAccel_Safe_windowB
import Mathlib.Tactic
open scoped RealInnerProductSpace
open InnerProductSpace AndersonAccel.Safe

private theorem gs_inner {n : ℕ} (s : ℕ → EuclideanSpace ℝ (Fin n)) (i : ℕ) :
    ⟪windowShat s i,s i⟫ = ‖windowShat s i‖^2 := by
  rw [gramSchmidt_def'' ℝ s i]
  simp only [inner_add_right,inner_sum,real_inner_smul_right,RCLike.ofReal_real_eq_id, id_eq]
  have hz : ∑ j ∈ Finset.Iio i, (⟪gramSchmidt ℝ s j,s i⟫/‖gramSchmidt ℝ s j‖^2)*
      ⟪windowShat s i,gramSchmidt ℝ s j⟫ = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [show ⟪windowShat s i,gramSchmidt ℝ s j⟫ = 0 from
      gramSchmidt_orthogonal ℝ s (by have := Finset.mem_Iio.mp hj; omega)]
    simp
  rw [hz,add_zero]
  exact real_inner_self_eq_norm_sq _

private theorem phi_bounds (θ η : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    0 < phiTheta θ η ∧ phiTheta θ η ≤ 1+θ := by
  unfold phiTheta
  split_ifs with h
  · constructor <;> linarith
  · have hη := abs_lt.mp (lt_of_not_ge h)
    have hd : 0 < 1-η := by linarith
    unfold signOne
    split_ifs with h0
    · constructor
      · exact div_pos (by linarith) hd
      · apply (div_le_iff₀ hd).mpr
        have hh := mul_pos (by linarith : 0 < θ) (by linarith : 0 < 1-η)
        nlinarith
    · constructor
      · apply div_pos _ hd; linarith
      · apply (div_le_iff₀ hd).mpr
        nlinarith [mul_nonneg (by linarith : 0 ≤ -η) (by linarith : 0 ≤ 1+θ)]

private theorem window_step {n : ℕ} (θ τ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hτ : 0 < τ) (s y : ℕ → EuclideanSpace ℝ (Fin n)) (i : ℕ)
    (hwd : ⟪windowShat s i,s i⟫ ≠ 0) (hy : ‖y i‖ ≤ 2*‖s i‖)
    (hs : τ*‖s i‖ ≤ ‖windowShat s i‖) :
    ‖windowB θ s y (i+1)‖+2 ≤ ((1+θ+τ)/τ)*(‖windowB θ s y i‖+2) := by
  let B := windowB θ s y i
  let sh := windowShat s i
  let η := ⟪sh,(Ring.inverse B) (y i)⟫/‖sh‖^2
  let t := phiTheta θ η
  have ht0 : 0 < t := (phi_bounds θ η hθ0 hθ1).1
  have ht1 : t ≤ 1+θ := (phi_bounds θ η hθ0 hθ1).2
  have hsh : 0 < ‖sh‖ := by
    have hh := gs_inner s i
    change ⟪windowShat s i,s i⟫ = ‖sh‖^2 at hh
    rw [hh] at hwd
    exact lt_of_le_of_ne (norm_nonneg _) (by intro he; apply hwd; rw [← he]; norm_num)
  have hs0 : 0 ≤ ‖s i‖ := norm_nonneg _
  have hB0 : 0 ≤ ‖B‖ := norm_nonneg _
  have he : t • y i+(1-t) • B (s i)-B (s i) = t • (y i-B (s i)) := by module
  have hupdate : windowB θ s y (i+1) = B+(‖sh‖^2)⁻¹ • rankOne ℝ (t • (y i-B (s i))) sh := by
    rw [windowB]
    change B+⟪windowShat s i,s i⟫⁻¹ • rankOne ℝ (t • y i+(1-t) • B (s i)-B (s i)) sh = _
    rw [gs_inner,he]
  have hn := norm_add_le B ((‖sh‖^2)⁻¹ • rankOne ℝ (t • (y i-B (s i))) sh)
  rw [← hupdate,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (sq_pos_of_pos hsh)),
    norm_rankOne,norm_smul,Real.norm_eq_abs,abs_of_pos ht0] at hn
  have hdiff : ‖y i-B (s i)‖ ≤ (2+‖B‖)*‖s i‖ := by
    have hh := norm_sub_le (y i) (B (s i))
    have hh' := B.le_opNorm (s i)
    nlinarith
  have hmul : (‖sh‖^2)⁻¹*(t*‖y i-B (s i)‖*‖sh‖) ≤
      (1+θ)/τ*(2+‖B‖) := by
    have hn' : (‖sh‖^2)⁻¹*(t*‖y i-B (s i)‖*‖sh‖) = t*‖y i-B (s i)‖/‖sh‖ := by field_simp <;> ring
    rw [hn']
    apply (div_le_iff₀ hsh).mpr
    have h1 := mul_le_mul_of_nonneg_left hdiff ht0.le
    have h2 := mul_le_mul_of_nonneg_right ht1 (mul_nonneg (by positivity : 0 ≤ 2+‖B‖) hs0)
    have h3 := mul_le_mul_of_nonneg_left hs (show 0 ≤ (1+θ)/τ*(2+‖B‖) by positivity)
    have hid : (1+θ)/τ*(2+‖B‖)*(τ*‖s i‖) = (1+θ)*((2+‖B‖)*‖s i‖) := by field_simp <;> ring
    rw [hid] at h3
    nlinarith
  have hid : ((1+θ+τ)/τ)*(‖B‖+2) = ‖B‖+2+(1+θ)/τ*(2+‖B‖) := by field_simp <;> ring
  change ‖windowB θ s y (i+1)‖+2 ≤ ((1+θ+τ)/τ)*(‖B‖+2)
  rw [hid]
  linarith

theorem solution {n : ℕ} (θbar τ : ℝ) (m : ℕ) (hθ0 : 0 < θbar) (hθ1 : θbar < 1)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hm : 1 ≤ m)
    (s y : ℕ → EuclideanSpace ℝ (Fin n)) (mk : ℕ) (hmk : mk ≤ m)
    (hwd : ∀ i < mk, inner ℝ (windowShat s i) (s i) ≠ 0)
    (hy : ∀ i < mk, ‖y i‖ ≤ 2 * ‖s i‖)
    (hτs : ∀ i < mk, τ * ‖s i‖ ≤ ‖windowShat s i‖) :
    ‖windowB θbar s y mk‖ ≤ 3 * ((1 + θbar + τ) / τ) ^ m - 2 := by
  let a := (1+θbar+τ)/τ
  have ha : 1 ≤ a := (le_div_iff₀ hτ0).mpr (by linarith)
  have hi : ∀ i ≤ mk,‖windowB θbar s y i‖+2 ≤ 3*a^i := by
    intro i
    induction i with
    | zero => intro _; simp only [windowB,pow_zero,mul_one]; have := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n)); change ‖(1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ ≤ 1 at this; linarith
    | succ i ih =>
      intro hik
      have him : i < mk := by omega
      have hh := window_step θbar τ hθ0 hθ1 hτ0 s y i (hwd i him) (hy i him) (hτs i him)
      have hh' := mul_le_mul_of_nonneg_left (ih (by omega)) (le_trans zero_le_one ha)
      rw [pow_succ]
      change ‖windowB θbar s y (i+1)‖+2 ≤ 3*(a^i*a)
      nlinarith
  have hh := hi mk le_rfl
  have hh' := pow_le_pow_right₀ ha hmk
  change ‖windowB θbar s y mk‖ ≤ 3*a^m-2
  linarith
