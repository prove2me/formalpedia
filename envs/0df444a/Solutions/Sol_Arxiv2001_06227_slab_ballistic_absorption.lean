-- Prove2me | solution 1 for Arxiv2001_06227.slab_ballistic_absorption
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T02:55:05.16954+00:00
-- url     : https://prove2.me/submissions/05390e94-5975-4c9a-8d3c-66c33502546c

import Mathlib
import Definitions.Def_Arxiv2001_06227_Basic

set_option autoImplicit false

open MeasureTheory Filter Topology Set

namespace S76SB

lemma sol (ellE I0 : ℝ) (hellE : 0 < ellE) (I : ℝ → ℝ)
    (hrte : ∀ s, 0 ≤ s → HasDerivWithinAt I (-(I s / ellE)) (Set.Ici 0) s)
    (hinit : I 0 = I0) : ∀ s, 0 ≤ s → I s = I0 * Real.exp (-(s / ellE)) := by
  set g : ℝ → ℝ := fun s => I s * Real.exp (s / ellE) with hg
  have hd : ∀ s, 0 ≤ s → HasDerivWithinAt g 0 (Set.Ici 0) s := by
    intro s hs
    have he : HasDerivAt (fun s => Real.exp (s / ellE)) (Real.exp (s / ellE) * (1 / ellE)) s := by
      have := ((hasDerivAt_id s).div_const ellE).exp
      simpa using this
    have h2 := (hrte s hs).mul he.hasDerivWithinAt
    have e : -(I s / ellE) * Real.exp (s / ellE) + I s * (Real.exp (s / ellE) * (1 / ellE)) = 0 := by
      field_simp; ring
    rw [e] at h2; exact h2
  intro s hs
  have hc : ContinuousOn g (Icc 0 s) := by
    intro x hx
    exact ((hd x hx.1).continuousWithinAt).mono Icc_subset_Ici_self
  have key := constant_of_has_deriv_right_zero hc
    (fun x hx => (hd x hx.1).mono (Ici_subset_Ici.2 hx.1)) s ⟨hs, le_rfl⟩
  simp only [g, hinit, zero_div, Real.exp_zero, mul_one] at key
  have : I s = I s * Real.exp (s / ellE) * Real.exp (-(s / ellE)) := by
    rw [mul_assoc, ← Real.exp_add]; simp
  rw [this, key]

end S76SB

open Arxiv2001_06227 S76SB in
theorem solution (vE S I0 P0 ellE ellA : ℝ) (hvE : 0 < vE) (hS : 0 < S)
    (hI0 : 0 < I0) (hP0 : P0 = I0 * S) (hellE : 0 < ellE) (hea : ellE = ellA)
    (I : ℝ → ℝ) (hrte : ∀ s, 0 ≤ s → HasDerivWithinAt I (-(I s / ellE)) (Set.Ici 0) s)
    (hinit : I 0 = I0) :
    (∀ L, 0 < L → slabBallisticAbsorbed vE S ellE L I = P0 * (1 - Real.exp (-(L / ellA)))) ∧
    (∀ L, 0 < L → slabBallisticAbsorbed vE S ellE L I ≤ P0) ∧
    Tendsto (fun L => slabBallisticAbsorbed vE S ellE L I) atTop (𝓝 P0) := by
  subst hea
  have hs := sol ellE I0 hellE I hrte hinit
  have h1 : ∀ L, 0 < L → slabBallisticAbsorbed vE S ellE L I =
      P0 * (1 - Real.exp (-(L / ellE))) := by
    intro L hL
    unfold slabBallisticAbsorbed
    have hcongr : ∫ s in (0 : ℝ)..L, I s / vE =
        ∫ s in (0 : ℝ)..L, I0 / vE * Real.exp (-(s / ellE)) := by
      apply intervalIntegral.integral_congr
      intro s hs'
      rw [uIcc_of_le hL.le] at hs'
      simp only
      rw [hs s hs'.1]; ring
    have hF : ∀ x ∈ uIcc 0 L, HasDerivAt (fun s => -(ellE * Real.exp (-(s / ellE))))
        (Real.exp (-(x / ellE))) x := by
      intro x _
      have := (((hasDerivAt_id x).div_const ellE).neg.exp).const_mul ellE
      exact (this.neg).congr_deriv (by simp only [id, Pi.neg_apply]; field_simp)
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      (by apply Continuous.intervalIntegrable; fun_prop)
    rw [hcongr, intervalIntegral.integral_const_mul, hint, hP0]
    simp only [zero_div, neg_zero, Real.exp_zero, mul_one]
    field_simp
    ring
  refine ⟨h1, ?_, ?_⟩
  · intro L hL
    rw [h1 L hL]
    have : 0 < Real.exp (-(L / ellE)) := Real.exp_pos _
    have : 0 < P0 := by rw [hP0]; positivity
    nlinarith
  · have hlim : Tendsto (fun L => P0 * (1 - Real.exp (-(L / ellE)))) atTop (𝓝 P0) := by
      have h0 : Tendsto (fun L => Real.exp (-(L / ellE))) atTop (𝓝 0) := by
        apply Real.tendsto_exp_atBot.comp
        exact tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const hellE)
      have := (tendsto_const_nhds (x := (1:ℝ))).sub h0
      simpa using this.const_mul P0
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with L hL
    rw [h1 L hL]
