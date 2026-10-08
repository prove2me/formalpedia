-- Prove2me | solution 1 for AstrophysicalFluidDynamics.shock_second_law_compression
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T11:38:59.327992+00:00
-- url     : https://prove2.me/submissions/a4426e26-e532-498d-bb45-9ba040061387

import Definitions.Def_AstrophysicalFluidDynamics_ShockDefs
import Mathlib

open Filter Topology

namespace AstrophysicalFluidDynamics.P34036588

/-- The entropy function of the velocity ratio `t = u₂/u₁`. -/
lemma g_anti (γ x : ℝ) (hγ : 1 < γ) (hx : 1 < x) (hA : 0 < (γ + 1) - (γ - 1) * x) :
    Real.log ((γ + 1) - (γ - 1) * x) - Real.log ((γ + 1) * x - (γ - 1)) + γ * Real.log x < 0 := by
  set g : ℝ → ℝ := fun t =>
    Real.log ((γ + 1) - (γ - 1) * t) - Real.log ((γ + 1) * t - (γ - 1)) + γ * Real.log t with hg
  have pos : ∀ t, 1 ≤ t → t ≤ x →
      0 < (γ + 1) - (γ - 1) * t ∧ 0 < (γ + 1) * t - (γ - 1) ∧ 0 < t := by
    intro t h1 h2
    refine ⟨by nlinarith, by nlinarith, by linarith⟩
  have hd : ∀ t, 1 ≤ t → t ≤ x → HasDerivAt g
      (-(γ - 1) / ((γ + 1) - (γ - 1) * t) - (γ + 1) / ((γ + 1) * t - (γ - 1)) + γ * t⁻¹) t := by
    intro t h1 h2
    obtain ⟨pA, pB, pt⟩ := pos t h1 h2
    have dA : HasDerivAt (fun t : ℝ => (γ + 1) - (γ - 1) * t) (-(γ - 1)) t := by
      simpa using ((hasDerivAt_id t).const_mul (γ - 1)).const_sub (γ + 1)
    have dB : HasDerivAt (fun t : ℝ => (γ + 1) * t - (γ - 1)) (γ + 1) t := by
      simpa using ((hasDerivAt_id t).const_mul (γ + 1)).sub_const (γ - 1)
    have := ((dA.log pA.ne').sub (dB.log pB.ne')).add ((Real.hasDerivAt_log pt.ne').const_mul γ)
    exact this
  have hcont : ContinuousOn g (Set.Icc 1 x) := by
    intro t ht
    exact (hd t ht.1 ht.2).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn g (Set.Icc 1 x) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 1 x) hcont
    intro t ht
    rw [interior_Icc] at ht
    obtain ⟨pA, pB, pt⟩ := pos t ht.1.le ht.2.le
    rw [(hd t ht.1.le ht.2.le).deriv]
    have key : (-(γ - 1) / ((γ + 1) - (γ - 1) * t) - (γ + 1) / ((γ + 1) * t - (γ - 1))
        + γ * t⁻¹) * (((γ + 1) - (γ - 1) * t) * ((γ + 1) * t - (γ - 1)) * t)
        = -γ * (γ ^ 2 - 1) * (t - 1) ^ 2 := by
      field_simp
      ring
    have hneg : -γ * (γ ^ 2 - 1) * (t - 1) ^ 2 < 0 := by
      have h1 : 0 < γ * (γ ^ 2 - 1) := by nlinarith
      have h2 : 0 < (t - 1) ^ 2 := by have : 0 < t - 1 := by linarith [ht.1]
                                      positivity
      nlinarith
    rw [← key] at hneg
    exact neg_of_mul_neg_left hneg (by positivity)
  have h1 : g x < g 1 := hanti ⟨le_refl 1, hx.le⟩ ⟨hx.le, le_refl x⟩ hx
  have hg1 : g 1 = 0 := by
    simp only [hg]
    norm_num
  simpa [hg, hg1] using h1

end AstrophysicalFluidDynamics.P34036588

open AstrophysicalFluidDynamics in
theorem solution
    (γ ρ₁ u₁ p₁ ρ₂ u₂ p₂ : ℝ) (hγ : 1 < γ)
    (hρ₁ : 0 < ρ₁) (hu₁ : 0 < u₁) (hp₁ : 0 < p₁)
    (hρ₂ : 0 < ρ₂) (hu₂ : 0 < u₂) (hp₂ : 0 < p₂)
    (hRH : RankineHugoniot γ ρ₁ u₁ p₁ ρ₂ u₂ p₂)
    (hshock : (ρ₂, u₂, p₂) ≠ (ρ₁, u₁, p₁))
    (hentropy : 0 ≤ entropyJumpOverCv γ ρ₁ p₁ ρ₂ p₂) :
    1 < machNumber γ ρ₁ u₁ p₁ ∧ machNumber γ ρ₂ u₂ p₂ < 1 ∧ ρ₁ < ρ₂ ∧ p₁ < p₂ := by
  obtain ⟨m1, h2, h3⟩ := hRH
  unfold perfectGasEnthalpy at h3
  have hγ1 : 0 < γ - 1 := by linarith
  have hj : 0 < ρ₁ * u₁ := mul_pos hρ₁ hu₁
  have mom : p₂ = p₁ + ρ₁ * u₁ * (u₁ - u₂) := by linear_combination h2 - u₂ * m1
  rw [m1] at h3
  have e := mul_left_cancel₀ hj.ne' h3
  have hc : γ / (γ - 1) * (γ - 1) = γ := by field_simp
  have e' : (γ - 1) * u₂ ^ 2 + 2 * γ * (p₂ / ρ₂) = (γ - 1) * u₁ ^ 2 + 2 * γ * (p₁ / ρ₁) := by
    linear_combination 2 * (γ - 1) * e - 2 * (p₂ / ρ₂ - p₁ / ρ₁) * hc
  have hq2 : p₂ / ρ₂ * (ρ₁ * u₁) = p₂ * u₂ := by rw [← m1]; field_simp
  have hq1 : p₁ / ρ₁ * (ρ₁ * u₁) = p₁ * u₁ := by field_simp
  have en : (γ - 1) * (ρ₁ * u₁) * u₂ ^ 2 + 2 * γ * p₂ * u₂
      = (γ - 1) * (ρ₁ * u₁) * u₁ ^ 2 + 2 * γ * p₁ * u₁ := by
    linear_combination (ρ₁ * u₁) * e' - 2 * γ * hq2 + 2 * γ * hq1
  have fac : (u₂ - u₁) * ((γ + 1) * ρ₁ * u₁ * u₂ - (γ - 1) * ρ₁ * u₁ ^ 2 - 2 * γ * p₁) = 0 := by
    linear_combination -en + 2 * γ * u₂ * mom
  have hne : u₂ ≠ u₁ := by
    intro h
    apply hshock
    have hr : ρ₂ = ρ₁ := by
      rw [h] at m1
      exact mul_right_cancel₀ hu₁.ne' m1
    have hp : p₂ = p₁ := by rw [mom, h]; ring
    rw [hr, h, hp]
  have K : (γ + 1) * ρ₁ * u₁ * u₂ = (γ - 1) * ρ₁ * u₁ ^ 2 + 2 * γ * p₁ := by
    have := (mul_eq_zero.mp fac).resolve_left (sub_ne_zero.mpr hne)
    linarith
  -- main claim: u₂ < u₁
  have hlt : u₂ < u₁ := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact h
    exfalso
    set x := u₂ / u₁ with hx
    have hx1 : 1 < x := by rw [hx, lt_div_iff₀ hu₁]; linarith
    have hxpos : 0 < x := by linarith
    have hu2 : u₂ = x * u₁ := by rw [hx]; field_simp
    -- ρ₂/ρ₁ = 1/x
    have hr : ρ₂ / ρ₁ = x⁻¹ := by
      rw [hu2] at m1
      field_simp
      nlinarith [m1]
    have hB : ((γ + 1) * x - (γ - 1)) * (ρ₁ * u₁ ^ 2) = 2 * γ * p₁ := by
      rw [hu2] at K; linear_combination K
    have hBpos : 0 < (γ + 1) * x - (γ - 1) := by
      by_contra hcon
      push Not at hcon
      have : ((γ + 1) * x - (γ - 1)) * (ρ₁ * u₁ ^ 2) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hcon (by positivity)
      nlinarith
    have hP : p₂ * ((γ + 1) * x - (γ - 1)) = p₁ * ((γ + 1) - (γ - 1) * x) := by
      rw [mom, hu2]
      linear_combination (1 - x) * hB
    have hApos : 0 < (γ + 1) - (γ - 1) * x := by
      have : 0 < p₂ * ((γ + 1) * x - (γ - 1)) := mul_pos hp₂ hBpos
      rw [hP] at this
      exact pos_of_mul_pos_right this hp₁.le
    have hpr : p₂ / p₁ = ((γ + 1) - (γ - 1) * x) / ((γ + 1) * x - (γ - 1)) := by
      rw [div_eq_div_iff hp₁.ne' hBpos.ne']
      linarith [hP]
    have hent : entropyJumpOverCv γ ρ₁ p₁ ρ₂ p₂
        = Real.log ((γ + 1) - (γ - 1) * x) - Real.log ((γ + 1) * x - (γ - 1))
          + γ * Real.log x := by
      unfold entropyJumpOverCv
      rw [hpr, hr, Real.log_div hApos.ne' hBpos.ne', Real.log_inv]
      ring
    have := P34036588.g_anti γ x hγ hx1 hApos
    linarith
  have hjK : (γ + 1) * ρ₁ * u₁ * u₂ < (γ + 1) * ρ₁ * u₁ * u₁ := by
    have : 0 < (γ + 1) * ρ₁ * u₁ := by positivity
    exact mul_lt_mul_of_pos_left hlt this
  have hM1 : γ * p₁ < ρ₁ * u₁ ^ 2 := by nlinarith
  have hp12 : p₁ < p₂ := by
    rw [mom]; have : 0 < ρ₁ * u₁ * (u₁ - u₂) := mul_pos hj (by linarith)
    linarith
  have hr12 : ρ₁ < ρ₂ := by
    by_contra hcon
    push Not at hcon
    have : ρ₂ * u₂ < ρ₁ * u₁ := by
      calc ρ₂ * u₂ ≤ ρ₁ * u₂ := mul_le_mul_of_nonneg_right hcon hu₂.le
        _ < ρ₁ * u₁ := mul_lt_mul_of_pos_left hlt hρ₁
    linarith
  have hss1 : 0 < soundSpeedSq γ p₁ ρ₁ := by unfold soundSpeedSq; positivity
  have hss2 : 0 < soundSpeedSq γ p₂ ρ₂ := by unfold soundSpeedSq; positivity
  refine ⟨?_, ?_, hr12, hp12⟩
  · unfold machNumber soundSpeed
    rw [one_lt_div (Real.sqrt_pos.mpr hss1), Real.sqrt_lt' hu₁]
    unfold soundSpeedSq
    rw [div_lt_iff₀ hρ₁]
    linarith
  · unfold machNumber soundSpeed
    rw [div_lt_one (Real.sqrt_pos.mpr hss2), Real.lt_sqrt hu₂.le]
    unfold soundSpeedSq
    rw [lt_div_iff₀ hρ₂]
    -- ρ₂ u₂² = ρ₁ u₁ u₂ ; γ p₂ = γ p₁ + γ ρ₁ u₁ (u₁ - u₂)
    have e1 : u₂ ^ 2 * ρ₂ = ρ₁ * u₁ * u₂ := by linear_combination u₂ * m1
    rw [e1, mom]
    linarith [K, hM1]
