-- Prove2me | solution 1 for Arxiv1906_02603.burr_power_law_tail
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T19:42:21.042316+00:00
-- url     : https://prove2.me/submissions/4f963145-0684-4320-9275-e8db26dad7d7

import Mathlib
import Definitions.Def_Arxiv1906_02603_Basic

open MeasureTheory Filter Topology

namespace S69T
open Arxiv1906_02603

lemma sq_rpow (x b : ℝ) (hx : 0 ≤ x) : (x ^ 2) ^ b = x ^ (2 * b) := by
  rw [Real.rpow_mul hx, show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]

lemma ratio (lam b A : ℝ) (hlam : 0 < lam) (hb : 1 < b) (hA : 0 < A) :
    burrPdf lam b A / (2 * (b - 1) * lam ^ (2 * b - 2) * A * A ^ (-2 * b)) =
      1 / (1 + (lam / A) ^ 2) ^ b := by
  unfold burrPdf
  have hw : 0 < 1 + (lam / A) ^ 2 := by positivity
  have e : (A / lam) ^ 2 + 1 = (A / lam) ^ 2 * (1 + (lam / A) ^ 2) := by
    field_simp
  rw [e, Real.mul_rpow (by positivity) hw.le, sq_rpow _ _ (by positivity),
    Real.div_rpow hA.le hlam.le, Real.rpow_sub hlam, show -2 * b = -(2 * b) by ring,
    Real.rpow_neg hA.le]
  have h1 : 0 < A ^ (2 * b) := Real.rpow_pos_of_pos hA _
  have h2 : 0 < lam ^ (2 * b) := Real.rpow_pos_of_pos hlam _
  have h3 : 0 < (1 + (lam / A) ^ 2) ^ b := Real.rpow_pos_of_pos hw _
  have hb1 : 0 < b - 1 := by linarith
  rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  push_cast
  field_simp

end S69T

open Arxiv1906_02603 in
theorem solution (lam b : ℝ) (hlam : 0 < lam) (hb : 1 < b) :
    Asymptotics.IsEquivalent atTop (fun A : ℝ => burrPdf lam b A)
      (fun A : ℝ => 2 * (b - 1) * lam ^ (2 * b - 2) * A * A ^ (-2 * b)) := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  have hlim : Tendsto (fun A : ℝ => 1 / (1 + (lam / A) ^ 2) ^ b) atTop (𝓝 1) := by
    have h0 : Tendsto (fun A : ℝ => lam / A) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h1 : Tendsto (fun A : ℝ => 1 + (lam / A) ^ 2) atTop (𝓝 1) := by
      simpa using (h0.pow 2).const_add 1
    have h2 := (h1.rpow_const (p := b) (Or.inl one_ne_zero))
    simpa using h2.inv₀ (by simp)
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with A hA
  exact (S69T.ratio lam b A hlam hb hA).symm
