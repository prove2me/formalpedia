-- Prove2me | solution 1 for ApproachRegret.Calibration.claim1_l1_dist
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T17:10:36.836982+00:00
-- url     : https://prove2.me/submissions/d6e02636-d638-4d32-a5a2-ee5d4bfe6f85

import Mathlib
import Definitions.Def_ApproachRegret_Calibration_Game

set_option autoImplicit false

namespace ApproachRegret.Calibration.P79cb327a

open ApproachRegret.Calibration

lemma l1norm_nonneg' {n : ℕ} (x : ApproachRegret.ToOLO.E n) : 0 ≤ l1norm x := by
  unfold l1norm
  exact Finset.sum_nonneg (fun i _ => abs_nonneg _)

lemma l1norm_smul' {n : ℕ} (c : ℝ) (x : ApproachRegret.ToOLO.E n) :
    l1norm (c • x) = |c| * l1norm x := by
  unfold l1norm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [PiLp.smul_apply, abs_mul]

lemma l1norm_sub_ge {n : ℕ} (x y : ApproachRegret.ToOLO.E n) :
    l1norm x - l1norm y ≤ l1norm (x - y) := by
  unfold l1norm
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have h := abs_sub_abs_le_abs_sub (x i) (y i)
  simpa [PiLp.sub_apply] using h

end ApproachRegret.Calibration.P79cb327a

open ApproachRegret.Calibration.P79cb327a in
open ApproachRegret.Calibration in
theorem solution {n : ℕ} (x : ApproachRegret.ToOLO.E n) (ε : ℝ) (hε : 0 < ε) :
    IsLeast ((fun y => l1norm (x - y)) '' l1Ball n (ε / 2)) (max 0 (-(ε / 2) + l1norm x)) := by
  constructor
  · by_cases hx : l1norm x ≤ ε / 2
    · refine ⟨x, hx, ?_⟩
      have h0 : l1norm (x - x) = 0 := by
        simp [l1norm]
      simp only [h0]
      exact (max_eq_left (by linarith)).symm
    · replace hx : ε / 2 < l1norm x := not_le.mp hx
      have hpos : 0 < l1norm x := lt_trans (by linarith) hx
      set t : ℝ := (ε / 2) / l1norm x with ht
      have ht0 : 0 ≤ t := div_nonneg (by linarith) hpos.le
      have ht1 : t ≤ 1 := (div_le_one hpos).mpr hx.le
      refine ⟨t • x, ?_, ?_⟩
      · show l1norm (t • x) ≤ ε / 2
        rw [l1norm_smul', abs_of_nonneg ht0, ht, div_mul_cancel₀ _ hpos.ne']
      · show l1norm (x - t • x) = _
        have hxe : x - t • x = (1 - t) • x := by
          rw [sub_smul, one_smul]
        rw [hxe, l1norm_smul', abs_of_nonneg (by linarith), sub_mul, one_mul, ht,
          div_mul_cancel₀ _ hpos.ne', max_eq_right (by linarith)]
        ring
  · rintro v ⟨y, hy, rfl⟩
    have hy' : l1norm y ≤ ε / 2 := hy
    have h1 := l1norm_sub_ge x y
    have h2 : 0 ≤ l1norm (x - y) := l1norm_nonneg' _
    exact max_le h2 (by linarith)
