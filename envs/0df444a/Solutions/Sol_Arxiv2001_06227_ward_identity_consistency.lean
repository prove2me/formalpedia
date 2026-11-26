-- Prove2me | solution 1 for Arxiv2001_06227.ward_identity_consistency
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T03:01:01.761033+00:00
-- url     : https://prove2.me/submissions/a0cb1e2c-327e-488b-903f-54d39c056340

import Mathlib
import Definitions.Def_Arxiv2001_06227_Basic

set_option autoImplicit false

open MeasureTheory Filter Topology

lemma cim {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ} (hf : Integrable f μ) :
    (∫ x, f x ∂μ).im = ∫ x, (f x).im ∂μ := (integral_im hf).symm

open Arxiv2001_06227 in
theorem solution (sigma green : Space → ℂ) (gamma : Space → Space → ℝ)
    (intensity : Space → ℝ) (hI : ∀ k, 0 ≤ intensity k)
    (hsymm : ∀ k k', gamma k k' = gamma k' k)
    (hsigma : Integrable (fun k => sigma k * (intensity k : ℂ)))
    (hgamma : Integrable (fun q : Space × Space =>
      (starRingEnd ℂ) (green q.1) * (gamma q.1 q.2 : ℂ) * (intensity q.2 : ℂ))
      ((volume : Measure Space).prod volume)) :
    (((∫ k, sigma k * (intensity k : ℂ) / (8 * Real.pi ^ 3 : ℝ)) +
        ∫ k, ∫ k', (starRingEnd ℂ) (green k) * (gamma k k' : ℂ) * (intensity k' : ℂ) /
          ((8 * Real.pi ^ 3) ^ 2 : ℝ)).im = 0 →
      ∫ k, (sigma k).im * intensity k / (8 * Real.pi ^ 3) =
        ∫ k, ∫ k', (green k).im * gamma k k' * intensity k' / (8 * Real.pi ^ 3) ^ 2) ∧
    ((∀ k, (sigma k).im = ∫ k', (green k').im * gamma k k' / (8 * Real.pi ^ 3)) →
      ∫ k, (sigma k).im * intensity k / (8 * Real.pi ^ 3) =
        ∫ k, ∫ k', (green k).im * gamma k k' * intensity k' / (8 * Real.pi ^ 3) ^ 2) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 8 * Real.pi ^ 3 := ⟨_, rfl⟩
  rw [← hc]
  set f : Space × Space → ℂ := fun q =>
    (starRingEnd ℂ) (green q.1) * (gamma q.1 q.2 : ℂ) * (intensity q.2 : ℂ) with hf
  have hfim : ∀ q, (f q).im = -((green q.1).im * gamma q.1 q.2 * intensity q.2) := by
    intro q; simp [hf, Complex.mul_im, Complex.mul_re]
  -- real double integral as function of the complex one
  have hRHS : (∫ k, ∫ k', (green k).im * gamma k k' * intensity k' / c ^ 2) =
      -(∫ k, ∫ k', f (k, k')).im / c ^ 2 := by
    have hae : ∀ᵐ k ∂(volume : Measure Space),
        (∫ k', f (k, k')).im = -∫ k', (green k).im * gamma k k' * intensity k' := by
      filter_upwards [hgamma.prod_right_ae] with k hk
      rw [cim hk, ← integral_neg]
      congr 1; funext k'; rw [hfim]
    rw [cim hgamma.integral_prod_left]
    rw [integral_congr_ae hae, integral_neg, neg_neg, ← integral_div]
    congr 1; funext k
    rw [integral_div]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Complex.add_im] at h
    have hA : (∫ k, sigma k * (intensity k : ℂ) / (c : ℂ)).im =
        ∫ k, (sigma k).im * intensity k / c := by
      rw [cim (hsigma.div_const _)]
      congr 1; funext k; simp [Complex.div_ofReal_im]
    have hB : (∫ k, ∫ k', (starRingEnd ℂ) (green k) * (gamma k k' : ℂ) * (intensity k' : ℂ) /
        ((c ^ 2 : ℝ) : ℂ)).im = (∫ k, ∫ k', f (k, k')).im / c ^ 2 := by
      have : (∫ k, ∫ k', (starRingEnd ℂ) (green k) * (gamma k k' : ℂ) * (intensity k' : ℂ) /
          ((c ^ 2 : ℝ) : ℂ)) = (∫ k, ∫ k', f (k, k')) / ((c ^ 2 : ℝ) : ℂ) := by
        rw [← integral_div]; congr 1; funext k; rw [← integral_div]
      rw [this, Complex.div_ofReal_im]
    rw [hA, hB] at h
    rw [hRHS]
    linear_combination h
  · rw [hRHS]
    have hL : (∫ k, (sigma k).im * intensity k / c) =
        ∫ k, ∫ k', (green k').im * gamma k k' * intensity k / c ^ 2 := by
      congr 1; funext k
      rw [h k, ← integral_mul_const, ← integral_div]
      congr 1; funext k'
      field_simp
    rw [hL]
    have hint : Integrable (Function.uncurry fun k k' : Space =>
        (green k').im * gamma k k' * intensity k / c ^ 2)
        ((volume : Measure Space).prod volume) := by
      have h2 := ((hgamma.im.neg).div_const (c ^ 2)).swap
      refine h2.congr (Eventually.of_forall fun q => ?_)
      show -(f q.swap).im / c ^ 2 = (green q.2).im * gamma q.1 q.2 * intensity q.1 / c ^ 2
      rw [hfim]; simp only [Prod.fst_swap, Prod.snd_swap]; rw [hsymm q.2 q.1]; ring
    rw [integral_integral_swap hint]
    have hR : (∫ k, ∫ k', f (k, k')).im = -∫ k, ∫ k', (green k).im * gamma k k' * intensity k' := by
      rw [cim hgamma.integral_prod_left, ← integral_neg]
      apply integral_congr_ae
      filter_upwards [hgamma.prod_right_ae] with k hk
      rw [cim hk, ← integral_neg]
      congr 1; funext k'; rw [hfim]
    rw [hR, neg_neg, ← integral_div]
    congr 1; funext k
    rw [← integral_div]
    congr 1; funext k'
    rw [hsymm]
