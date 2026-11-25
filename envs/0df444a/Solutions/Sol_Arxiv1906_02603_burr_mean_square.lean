-- Prove2me | solution 1 for Arxiv1906_02603.burr_mean_square
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T19:44:31.742476+00:00
-- url     : https://prove2.me/submissions/ec89f2a1-4577-4b1d-b2cc-8e3ce6e9362a

import Mathlib
import Definitions.Def_Arxiv1906_02603_Basic

open MeasureTheory Filter Topology Set

namespace S69M
open Arxiv1906_02603

noncomputable def F (lam b A : ℝ) : ℝ :=
  lam ^ 2 * (b - 1) * ((1 + (A / lam) ^ 2) ^ (2 - b) / (2 - b) + (1 + (A / lam) ^ 2) ^ (1 - b) / (b - 1))

lemma hd (lam b A : ℝ) (hlam : 0 < lam) (hb : 2 < b) :
    HasDerivAt (F lam b) (A ^ 2 * burrPdf lam b A) A := by
  have hw : 0 < 1 + (A / lam) ^ 2 := by positivity
  have h1 : HasDerivAt (fun x => 1 + (x / lam) ^ 2) (2 * (A / lam) * (1 / lam)) A := by
    have := ((hasDerivAt_id A).div_const lam).pow 2
    simpa [mul_comm] using this.const_add 1
  have ha := h1.rpow_const (p := 2 - b) (Or.inl hw.ne')
  have hc := h1.rpow_const (p := 1 - b) (Or.inl hw.ne')
  have h := ((ha.div_const (2 - b)).add (hc.div_const (b - 1))).const_mul (lam ^ 2 * (b - 1))
  unfold F
  refine h.congr_deriv ?_
  unfold burrPdf
  rw [show 2 - b - 1 = 1 - b by ring, show 1 - b - 1 = -b by ring, Real.rpow_neg hw.le,
    Real.rpow_sub hw, Real.rpow_one, add_comm ((A / lam) ^ 2) 1]
  have hq : 0 < (1 + (A / lam) ^ 2) ^ b := Real.rpow_pos_of_pos hw b
  have h2 : (2 - b) ≠ 0 := by linarith
  have h3 : (b - 1) ≠ 0 := by linarith
  field_simp
  ring

lemma lim (lam b : ℝ) (hlam : 0 < lam) (hb : 2 < b) : Tendsto (F lam b) atTop (𝓝 0) := by
  have hw : Tendsto (fun A : ℝ => 1 + (A / lam) ^ 2) atTop atTop := by
    apply tendsto_atTop_add_const_left
    exact (tendsto_pow_atTop two_ne_zero).comp (tendsto_id.atTop_div_const hlam)
  have t1 := (tendsto_rpow_neg_atTop (y := b - 2) (by linarith)).comp hw
  have t2 := (tendsto_rpow_neg_atTop (y := b - 1) (by linarith)).comp hw
  have := ((t1.div_const (2 - b)).add (t2.div_const (b - 1))).const_mul (lam ^ 2 * (b - 1))
  simp only [zero_div, add_zero, mul_zero] at this
  refine this.congr' (Eventually.of_forall fun A => ?_)
  simp only [F, Function.comp, neg_sub]

end S69M

open Arxiv1906_02603 in
theorem solution (lam b : ℝ) (hlam : 0 < lam) (hb : 2 < b) :
    IntegrableOn (fun A : ℝ => A ^ 2 * burrPdf lam b A) (Ioi 0) ∧
    burrMoment lam b 2 = lam ^ 2 / (b - 2) := by
  have hderiv : ∀ x ∈ Ici (0:ℝ), HasDerivAt (S69M.F lam b) (x ^ 2 * burrPdf lam b x) x :=
    fun x _ => S69M.hd lam b x hlam hb
  have hpos : ∀ x ∈ Ioi (0:ℝ), 0 ≤ x ^ 2 * burrPdf lam b x := by
    intro x hx
    have hx : 0 < x := hx
    unfold burrPdf
    have : 0 < b - 1 := by linarith
    have : 0 < ((x / lam) ^ 2 + 1) ^ b := Real.rpow_pos_of_pos (by positivity) b
    positivity
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hderiv hpos (S69M.lim lam b hlam hb), ?_⟩
  unfold burrMoment
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos (S69M.lim lam b hlam hb)]
  simp only [S69M.F, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero, Real.one_rpow]
  have h2 : (2 - b) ≠ 0 := by linarith
  have h3 : (b - 1) ≠ 0 := by linarith
  have h4 : (b - 2) ≠ 0 := by linarith
  field_simp
  ring
