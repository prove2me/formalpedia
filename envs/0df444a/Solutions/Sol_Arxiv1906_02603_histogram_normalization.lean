-- Prove2me | solution 1 for Arxiv1906_02603.histogram_normalization
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T19:45:22.088095+00:00
-- url     : https://prove2.me/submissions/d6cc0eb6-7770-475b-805f-ff3f1398b679

import Mathlib
import Definitions.Def_Arxiv1906_02603_Basic

open MeasureTheory Filter Topology Set

namespace S69H
open Arxiv1906_02603

noncomputable def G (N0 A0 amin b A : ℝ) : ℝ :=
  -(N0 * ((A / A0) ^ 2 + amin) ^ (1 - b) / (b - 1))

lemma hd (N0 A0 amin b A : ℝ) (hA0 : 0 < A0) (hamin : 0 < amin) (hb : 1 < b) :
    HasDerivAt (G N0 A0 amin b) (ampHist N0 A0 amin b A) A := by
  have hw : 0 < (A / A0) ^ 2 + amin := by positivity
  have h1 : HasDerivAt (fun x => (x / A0) ^ 2 + amin) (2 * (A / A0) * (1 / A0)) A := by
    have := ((hasDerivAt_id A).div_const A0).pow 2
    simpa [mul_comm] using this.add_const amin
  have h := ((h1.rpow_const (p := 1 - b) (Or.inl hw.ne')).const_mul N0).div_const (b - 1) |>.neg
  unfold G
  refine h.congr_deriv ?_
  unfold ampHist
  rw [show 1 - b - 1 = -b by ring, Real.rpow_neg hw.le]
  have hq : 0 < ((A / A0) ^ 2 + amin) ^ b := Real.rpow_pos_of_pos hw b
  have h3 : (b - 1) ≠ 0 := by linarith
  field_simp
  ring

lemma lim (N0 A0 amin b : ℝ) (hA0 : 0 < A0) (hb : 1 < b) :
    Tendsto (G N0 A0 amin b) atTop (𝓝 0) := by
  have hw : Tendsto (fun A : ℝ => (A / A0) ^ 2 + amin) atTop atTop := by
    apply tendsto_atTop_add_const_right
    exact (tendsto_pow_atTop two_ne_zero).comp (tendsto_id.atTop_div_const hA0)
  have t := (tendsto_rpow_neg_atTop (y := b - 1) (by linarith)).comp hw
  have := ((t.const_mul N0).div_const (b - 1)).neg
  simp only [mul_zero, zero_div, neg_zero] at this
  refine this.congr' (Eventually.of_forall fun A => ?_)
  simp only [G, Function.comp, neg_sub]

end S69H

open Arxiv1906_02603 in
theorem solution (N0 A0 amin b : ℝ) (hN0 : 0 < N0) (hA0 : 0 < A0)
    (hamin : 0 < amin) (hb : 1 < b) :
    IntegrableOn (ampHist N0 A0 amin b) (Ioi 0) ∧
    ∫ A in Ioi (0 : ℝ), ampHist N0 A0 amin b A = N0 / ((b - 1) * amin ^ (b - 1)) ∧
    (∀ A : ℝ, normHist A0 amin b A = ampHist N0 A0 amin b A / (N0 / ((b - 1) * amin ^ (b - 1)))) ∧
    ∫ A in Ioi (0 : ℝ), normHist A0 amin b A = 1 := by
  have hderiv : ∀ x ∈ Ici (0:ℝ), HasDerivAt (S69H.G N0 A0 amin b) (ampHist N0 A0 amin b x) x :=
    fun x _ => S69H.hd N0 A0 amin b x hA0 hamin hb
  have hpos : ∀ x ∈ Ioi (0:ℝ), 0 ≤ ampHist N0 A0 amin b x := by
    intro x hx
    have hx : 0 < x := hx
    unfold ampHist
    have : 0 < ((x / A0) ^ 2 + amin) ^ b := Real.rpow_pos_of_pos (by positivity) b
    positivity
  have hb1 : (b - 1) ≠ 0 := by linarith
  have hm : 0 < amin ^ (b - 1) := Real.rpow_pos_of_pos hamin _
  have hI : ∫ A in Ioi (0 : ℝ), ampHist N0 A0 amin b A = N0 / ((b - 1) * amin ^ (b - 1)) := by
    rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos (S69H.lim N0 A0 amin b hA0 hb)]
    simp only [S69H.G, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_add, sub_neg_eq_add]
    rw [show 1 - b = -(b - 1) by ring, Real.rpow_neg hamin.le]
    field_simp
  have h3 : ∀ A : ℝ, normHist A0 amin b A =
      ampHist N0 A0 amin b A / (N0 / ((b - 1) * amin ^ (b - 1))) := by
    intro A
    unfold normHist ampHist
    field_simp
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hderiv hpos (S69H.lim N0 A0 amin b hA0 hb), hI, h3, ?_⟩
  simp_rw [h3]
  rw [integral_div, hI, div_self]
  positivity
