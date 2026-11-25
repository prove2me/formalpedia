-- Prove2me | solution 1 for Arxiv1507_03491.window_conditions
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T20:57:42.166694+00:00
-- url     : https://prove2.me/submissions/ada38c80-25a5-4879-b7f8-808d4d1e7831

import Mathlib
import Definitions.Def_Arxiv1507_03491_Basic

open MeasureTheory Filter Topology Set
open scoped ContDiff NNReal

namespace S70WC
open Arxiv1507_03491

lemma psi_eq : bumpPsi = fun x => expNegInvGlue (1 - x ^ 2) := by
  funext x
  unfold bumpPsi expNegInvGlue
  by_cases hx : |x| < 1
  · have : 0 < 1 - x ^ 2 := by
      have := abs_lt.1 hx; nlinarith
    rw [if_pos hx, if_neg (not_le.2 this)]; congr 1; field_simp
  · have : 1 - x ^ 2 ≤ 0 := by
      push Not at hx
      have : 1 ≤ x ^ 2 := by
        have h := sq_abs x
        nlinarith [abs_nonneg x]
      linarith
    rw [if_neg hx, if_pos this]

lemma psi_cont : Continuous bumpPsi := by
  rw [psi_eq]; exact ((expNegInvGlue.contDiff (n := 0)).continuous).comp (by fun_prop)

lemma psi_contDiff : ContDiff ℝ ∞ bumpPsi := by
  rw [psi_eq]; exact (expNegInvGlue.contDiff (n := ⊤)).comp (by fun_prop)

lemma psi_zero {t : ℝ} (ht : 1 ≤ |t|) : bumpPsi t = 0 := by
  unfold bumpPsi; rw [if_neg (not_lt.2 ht)]

lemma psi_even (t : ℝ) : bumpPsi (-t) = bumpPsi t := by
  unfold bumpPsi; simp

lemma psi_pos {t : ℝ} (ht : |t| < 1) : 0 < bumpPsi t := by
  unfold bumpPsi; rw [if_pos ht]; exact Real.exp_pos _

noncomputable def F (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, bumpPsi t

lemma F_contDiff : ContDiff ℝ ∞ F := by
  have hd : ∀ x, HasDerivAt F (bumpPsi x) x := fun x =>
    (psi_cont.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hderiv : deriv F = bumpPsi := funext fun x => (hd x).deriv
  rw [contDiff_infty_iff_deriv]
  exact ⟨fun x => (hd x).differentiableAt, hderiv ▸ psi_contDiff⟩

lemma F_one_pos : 0 < F 1 := by
  unfold F
  apply intervalIntegral.intervalIntegral_pos_of_pos_on (psi_cont.intervalIntegrable _ _) _ one_pos
  intro x hx
  apply psi_pos
  rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]

lemma F_ge {x : ℝ} (hx : 1 ≤ x) : F x = F 1 := by
  unfold F
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1) (psi_cont.intervalIntegrable _ _)
    (psi_cont.intervalIntegrable _ _)]
  have : ∫ t in (1 : ℝ)..x, bumpPsi t = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro t ht
      rw [uIcc_of_le hx] at ht
      apply psi_zero
      rw [abs_of_nonneg (by linarith [ht.1])]; exact ht.1
  rw [this, add_zero]

lemma F_le {x : ℝ} (hx : x ≤ -1) : F x = -F 1 := by
  have h1 : F x = F (-1) := by
    unfold F
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := -1) (psi_cont.intervalIntegrable _ _)
      (psi_cont.intervalIntegrable _ _)]
    have : ∫ t in (-1 : ℝ)..x, bumpPsi t = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
      · simp
      · intro t ht
        rw [uIcc_of_ge hx] at ht
        apply psi_zero
        rw [abs_of_nonpos (by linarith [ht.2])]; linarith [ht.2]
    rw [this, add_zero]
  rw [h1]
  unfold F
  rw [intervalIntegral.integral_symm]
  congr 1
  have := intervalIntegral.integral_comp_neg (a := 0) (b := 1) (fun t => bumpPsi t)
  simp only [psi_even, neg_zero] at this
  exact this.symm

lemma A_eq : bumpA = F 1 := rfl

lemma phi_eq (x : ℝ) : bumpPhi x = (1 / F 1) * F x := rfl

lemma phi_ge {x : ℝ} (hx : 1 ≤ x) : bumpPhi x = 1 := by
  rw [phi_eq, F_ge hx]; field_simp [F_one_pos.ne']

lemma phi_le {x : ℝ} (hx : x ≤ -1) : bumpPhi x = -1 := by
  rw [phi_eq, F_le hx]; field_simp [F_one_pos.ne']

end S70WC

open Arxiv1507_03491 S70WC in
theorem solution (M0 : ℝ) (hM0 : 4 < M0) :
    ContDiff ℝ ∞ (window M0) ∧ tsupport (window M0) ⊆ Ioo (-M0) M0 ∧
    (∀ x : ℝ, x ≤ -(3 / 4 * M0) → window M0 x = 0) ∧
    (∀ x : ℝ, -(1 / 4 * M0) ≤ x → x ≤ 1 / 4 * M0 → window M0 x = 1) ∧
    (∀ x : ℝ, 3 / 4 * M0 ≤ x → window M0 x = 0) := by
  have hleft : ∀ x : ℝ, x ≤ -(3 / 4 * M0) → window M0 x = 0 := by
    intro x hx
    unfold window
    rw [phi_le (by linarith), phi_le (by linarith)]; ring
  have hright : ∀ x : ℝ, 3 / 4 * M0 ≤ x → window M0 x = 0 := by
    intro x hx
    unfold window
    rw [phi_ge (by linarith), phi_ge (by linarith)]; ring
  refine ⟨?_, ?_, hleft, ?_, hright⟩
  · have hphi : bumpPhi = fun x => (1 / F 1) * F x := rfl
    unfold window
    rw [hphi]
    have hF := F_contDiff
    exact contDiff_const.mul (((contDiff_const.mul (hF.comp (contDiff_id.add contDiff_const)))).sub
      (contDiff_const.mul (hF.comp (contDiff_id.sub contDiff_const))))
  · have hsub : Function.support (window M0) ⊆ Icc (-(3 / 4 * M0)) (3 / 4 * M0) := by
      intro x hx
      by_contra hc
      rw [mem_Icc, not_and_or] at hc
      apply hx
      rcases hc with h | h
      · exact hleft x (by linarith [not_le.1 h])
      · exact hright x (by linarith [not_le.1 h])
    intro x hx
    have := closure_minimal hsub isClosed_Icc hx
    constructor <;> linarith [this.1, this.2]
  · intro x h1 h2
    unfold window
    rw [phi_ge (by linarith), phi_le (by linarith)]; ring
