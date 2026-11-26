-- Prove2me | solution 1 for Arxiv1901_08703.spline_basis_regularity_support
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T05:00:31.736282+00:00
-- url     : https://prove2.me/submissions/039a2728-d167-4f49-a77d-7fd7563006dd

import Mathlib
import Definitions.Def_Arxiv1901_08703_Basic

set_option autoImplicit false

open Set

namespace S78SP
open Arxiv1901_08703

lemma tp_nonpos (m : ℕ) (z : ℝ) (hz : z ≤ 0) (hm : 0 < m) : truncPow m z = 0 := by
  unfold truncPow
  split_ifs with h
  · have : z = 0 := le_antisymm hz h
    subst this; exact zero_pow hm.ne'
  · rfl

lemma tp_deriv (m : ℕ) (z : ℝ) :
    HasDerivAt (truncPow (m + 2)) (((m : ℝ) + 2) * truncPow (m + 1) z) z := by
  rcases lt_trichotomy z 0 with hz | rfl | hz
  · have h0 : truncPow (m + 1) z = 0 := tp_nonpos _ _ hz.le (by omega)
    rw [h0, mul_zero]
    have : truncPow (m + 2) =ᶠ[nhds z] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hz] with y hy
      exact tp_nonpos _ _ (le_of_lt hy) (by omega)
    exact (hasDerivAt_const z (0:ℝ)).congr_of_eventuallyEq this
  · have h0 : truncPow (m + 1) 0 = 0 := tp_nonpos _ _ le_rfl (by omega)
    rw [h0, mul_zero]
    have hl : HasDerivWithinAt (truncPow (m + 2)) 0 (Iic 0) 0 :=
      (hasDerivWithinAt_const (0:ℝ) _ (0:ℝ)).congr (fun y hy => tp_nonpos _ _ hy (by omega))
        (tp_nonpos _ _ le_rfl (by omega))
    have hr : HasDerivWithinAt (truncPow (m + 2)) 0 (Ici 0) 0 := by
      have := (hasDerivAt_pow (m + 2) (0:ℝ)).hasDerivWithinAt (s := Ici 0)
      simp only [zero_pow (show m + 2 - 1 ≠ 0 by omega), mul_zero] at this
      refine this.congr (fun y hy => ?_) ?_
      · simp [truncPow, show (0:ℝ) ≤ y from hy]
      · simp [truncPow]
    have := hl.union hr
    rw [Iic_union_Ici] at this
    exact this.hasDerivAt Filter.univ_mem
  · have hp : truncPow (m + 1) z = z ^ (m + 1) := by simp [truncPow, hz.le]
    rw [hp]
    have : truncPow (m + 2) =ᶠ[nhds z] fun y => y ^ (m + 2) := by
      filter_upwards [Ioi_mem_nhds hz] with y hy
      simp [truncPow, (le_of_lt (show (0:ℝ) < y from hy))]
    refine ((hasDerivAt_pow (m + 2) z).congr_of_eventuallyEq this).congr_deriv ?_
    push_cast; ring_nf

lemma tp_contDiff (m : ℕ) : ContDiff ℝ m (truncPow (m + 1)) := by
  induction m with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    have : truncPow 1 = fun z => max z 0 := by
      funext z; unfold truncPow
      split_ifs with h
      · simp [h]
      · simp [le_of_lt (not_le.1 h)]
    rw [this]; fun_prop
  | succ m ih =>
    have hd : deriv (truncPow (m + 2)) = fun z => ((m : ℝ) + 2) * truncPow (m + 1) z :=
      funext fun z => (tp_deriv m z).deriv
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiff_succ_iff_deriv]
    refine ⟨fun z => (tp_deriv m z).differentiableAt, by simp, ?_⟩
    rw [hd]
    exact contDiff_const.mul ih

lemma phi_zero_left (s : ℝ) (hs : s ≤ -5 / 2) : splinePhi 4 s = 0 := by
  unfold splinePhi
  refine Finset.sum_eq_zero (fun j hj => ?_)
  rw [tp_nonpos _ _ ?_ (by norm_num), mul_zero]
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  push_cast; linarith

lemma phi_zero_right (s : ℝ) (hs : 5 / 2 ≤ s) : splinePhi 4 s = 0 := by
  unfold splinePhi
  have hpos : ∀ j ∈ Finset.range (4 + 2), truncPow 4 (s + ((4:ℕ) + 1) / 2 - (j : ℝ)) =
      (s + ((4:ℕ) + 1) / 2 - (j : ℝ)) ^ 4 := by
    intro j hj
    have : (j : ℝ) ≤ 5 := by exact_mod_cast (show j ≤ 5 by simp at hj; omega)
    unfold truncPow; rw [if_pos (by push_cast; linarith)]
  rw [Finset.sum_congr rfl (fun j hj => by rw [hpos j hj])]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [Nat.choose, Nat.factorial]
  ring

end S78SP

open Arxiv1901_08703 in
theorem solution (R : ℝ) (hR : 0 < R) (M : ℕ) (hM : 1 ≤ M)
    (i : ℕ) (hi1 : 1 ≤ i) (hiM : i ≤ M) :
    ContDiff ℝ 3 (splineBasis R M i) ∧ tsupport (splineBasis R M i) ⊆ Set.Ioo (-R) R := by
  have hh : 0 < splineStep R M := by unfold splineStep; positivity
  constructor
  · unfold splineBasis splinePhi
    refine ContDiff.sum (fun j _ => ?_)
    refine contDiff_const.mul ?_
    have := S78SP.tp_contDiff 3
    exact this.comp (by fun_prop)
  · set h := splineStep R M with hh_def
    set c := splineKnot R M i with hc
    have hsub : Function.support (splineBasis R M i) ⊆ Icc (c - 5 / 2 * h) (c + 5 / 2 * h) := by
      intro t ht
      by_contra hn
      apply ht
      simp only [mem_Icc, not_and_or, not_le] at hn
      unfold splineBasis
      rcases hn with hn | hn
      · apply S78SP.phi_zero_left
        rw [div_le_iff₀ hh]; linarith
      · apply S78SP.phi_zero_right
        rw [le_div_iff₀ hh]; linarith
    refine (closure_minimal hsub isClosed_Icc).trans ?_
    intro t ht
    obtain ⟨h1, h2⟩ := ht
    have hi : (1 : ℝ) ≤ i := by exact_mod_cast hi1
    have hiM' : (i : ℝ) ≤ M := by exact_mod_cast hiM
    have hM5 : ((M : ℝ) + 5) * h = 2 * R := by
      simp only [hh_def, splineStep]; field_simp
    simp only [hc, splineKnot] at h1 h2
    constructor <;> nlinarith
