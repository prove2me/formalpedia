-- Prove2me | solution 1 for AnalyticGeometry.reduction_mod_p
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T20:16:31.082126+00:00
-- url     : https://prove2.me/submissions/9cefaab3-e982-453b-ae05-cad11e62bb2d

import Mathlib
import Definitions.Def_AnalyticGeometry_ZLaurentGT

set_option autoImplicit false

open Filter Topology

lemma AGaf_zpow_tendsto_zero {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) :
    Tendsto (fun n : ℤ => s ^ n) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℤ => n.toNat) atTop atTop :=
    tendsto_atTop_atTop.2 (fun b => ⟨b, fun n hn => by omega⟩)
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).comp ht
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℤ)] with n hn
  simp only [Function.comp_apply]
  rw [← zpow_natCast, Int.toNat_of_nonneg hn]

lemma AGaf_decays_of_bounded {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) (f : LaurentSeries ℤ) (C : ℝ)
    (hC : ∀ n, |(f.coeff n : ℝ)| ≤ C) : AnalyticGeometry.DecaysAt s f := by
  have := (AGaf_zpow_tendsto_zero h0 h1).const_mul C
  rw [mul_zero] at this
  refine squeeze_zero (fun n => ?_) (fun n => ?_) this
  · exact mul_nonneg (abs_nonneg _) (zpow_nonneg h0 n)
  · exact mul_le_mul_of_nonneg_right (hC n) (zpow_nonneg h0 n)

lemma AGaf_decays_mono {s : ℝ} (hs : 0 ≤ s) (f g : LaurentSeries ℤ)
    (hfg : ∀ n, |(g.coeff n : ℝ)| ≤ |(f.coeff n : ℝ)|) (hf : AnalyticGeometry.DecaysAt s f) :
    AnalyticGeometry.DecaysAt s g := by
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hf
  · exact mul_nonneg (abs_nonneg _) (zpow_nonneg hs n)
  · exact mul_le_mul_of_nonneg_right (hfg n) (zpow_nonneg hs n)

open AnalyticGeometry in
theorem solution (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (p : ℕ) (hp : p.Prime) :
    (∀ g : LaurentSeries (ZMod p), ∃ f ∈ zLaurentGT r,
        ∀ n : ℤ, ((f.coeff n : ZMod p)) = g.coeff n) ∧
      (∀ f ∈ zLaurentGT r, (∀ n : ℤ, ((f.coeff n : ZMod p)) = 0) →
        ∃ h ∈ zLaurentGT r, f = (p : LaurentSeries ℤ) * h) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  constructor
  · intro g
    let φ : ZeroHom (ZMod p) ℤ := ⟨fun a => (a.val : ℤ), by simp⟩
    refine ⟨g.map φ, ⟨(r + 1) / 2, by linarith,
      AGaf_decays_of_bounded (by linarith) (by linarith) _ p ?_⟩, fun n => ?_⟩
    · intro n
      simp only [HahnSeries.map_coeff, φ, ZeroHom.coe_mk, Int.cast_natCast, Nat.abs_cast]
      exact_mod_cast (ZMod.val_lt (g.coeff n)).le
    · simp [φ]
  · intro f hf hdiv
    obtain ⟨s, hs, hd⟩ := hf
    let ψ : ZeroHom ℤ ℤ := ⟨fun a => a / (p : ℤ), by simp⟩
    have hdvd : ∀ n, (p : ℤ) ∣ f.coeff n := fun n =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (hdiv n)
    refine ⟨f.map ψ, ⟨s, hs, AGaf_decays_mono (by linarith) f _ (fun n => ?_) hd⟩, ?_⟩
    · obtain ⟨k, hk⟩ := hdvd n
      simp only [HahnSeries.map_coeff, ψ, ZeroHom.coe_mk]
      rw [hk, Int.mul_ediv_cancel_left _ (by exact_mod_cast hp.ne_zero)]
      push_cast
      rw [abs_mul]
      have : (1 : ℝ) ≤ |(p : ℝ)| := by
        rw [abs_of_nonneg (by positivity)]; exact_mod_cast hp.one_lt.le
      nlinarith [abs_nonneg (k : ℝ)]
    · ext n
      rw [← nsmul_eq_mul, HahnSeries.coeff_nsmul]
      simp only [Pi.smul_apply, HahnSeries.map_coeff, ψ, ZeroHom.coe_mk, nsmul_eq_mul]
      exact (Int.mul_ediv_cancel' (hdvd n)).symm
