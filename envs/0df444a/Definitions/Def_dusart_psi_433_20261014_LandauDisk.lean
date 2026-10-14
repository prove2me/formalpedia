-- Prove2me | Definitions.Def_dusart_psi_433_20261014_LandauDisk
-- name    : dusart_psi_433_20261014_LandauDisk
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:23:08.015821+00:00
-- url     : https://prove2.me/theorems/ce9d9c83-36ea-4a3d-ad87-635cf6cb208e
-- title:
--   Dusart smoothing: Landau Disk
-- statement:
--   This module gives the complete landau disk component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_LandauBound
import Definitions.Def_dusart_psi_433_20261014_LandauSplit
/- Copyright (c) 2026 Anthropic PBC; Apache-2.0. -/
noncomputable section
namespace DusartSmoothing.Landau
open Complex Set Metric Filter Topology

/-- **Landau partial fraction, unit-disk form**: f analytic on the closed unit disk, f(0) = 1,
‖f‖ ≤ B on ‖z‖ ≤ 24/25 (2 ≤ B), finite zero set.  Then for ‖z‖ ≤ 83/100 with f(z) ≠ 0,
logDeriv f z is the sum of m_ρ/(z−ρ) over zeros with ‖ρ‖ ≤ 22/25, up to an error ≤ 44795000 log B. -/
theorem logDeriv_partial_fraction_unit {f : ℂ → ℂ} {B : ℝ}
    (hfa : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0 : f 0 = 1)
    (hfin : (SetOfZeros 1 f).Finite) (hB2 : 2 ≤ B)
    (hfB : ∀ w : ℂ, ‖w‖ ≤ 24/25 → ‖f w‖ ≤ B)
    {z : ℂ} (hz : ‖z‖ ≤ 83/100) (hfz : f z ≠ 0) :
    ‖logDeriv f z - ∑ ρ ∈ (finiteSetOfZeros_mono (by norm_num : (22/25:ℝ) < 1) hfin).toFinset,
        (analyticOrderNatAt f ρ : ℂ) / (z - ρ)‖ ≤ 44795000 * Real.log B := by
  have hf0' : f 0 ≠ 0 := by rw [hf0]; exact one_ne_zero
  have hsplit := logDeriv_split hfa hf0' (by norm_num : (22/25:ℝ) < 1) hfin
    (lt_of_le_of_lt hz (by norm_num)) hfz
  rw [hsplit]
  rw [add_sub_cancel_left]
  exact norm_logDeriv_Cf_le hfa hf0 hfin hB2 hfB hz





theorem logDeriv_partial_fraction_disk {f : ℂ → ℂ} {s₀ : ℂ} {R B : ℝ}
    (hR : 0 < R) (hfa : AnalyticOnNhd ℂ f (Metric.closedBall s₀ R)) (hf0 : f s₀ ≠ 0)
    (hB2 : 2 ≤ B) (hfB : ∀ w ∈ Metric.closedBall s₀ (24/25 * R), ‖f w‖ ≤ B * ‖f s₀‖) :
    ∃ Z : Finset ℂ,
      (↑Z = {ρ ∈ Metric.closedBall s₀ (22/25 * R) | f ρ = 0}) ∧
      ((∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) ≤ 1 / Real.log ((24/25) / (22/25)) * Real.log B) ∧
      ∀ s ∈ Metric.closedBall s₀ (83/100 * R), f s ≠ 0 →
        ‖logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖
          ≤ 44795000 / R * Real.log B := by
  have hRC : (R : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hR
  set φ : ℂ → ℂ := fun w => s₀ + (R : ℂ) * w with hφ
  have hφmem : ∀ {w : ℂ} {r : ℝ}, ‖w‖ ≤ r → φ w ∈ Metric.closedBall s₀ (r * R) := by
    intro w r hw
    rw [Metric.mem_closedBall, Complex.dist_eq, hφ]
    simp only [add_sub_cancel_left]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    calc R * ‖w‖ ≤ R * r := mul_le_mul_of_nonneg_left hw hR.le
      _ = r * R := mul_comm _ _
  set c : ℂ := (f s₀)⁻¹ with hc
  have hcne : c ≠ 0 := inv_ne_zero hf0
  set g : ℂ → ℂ := fun w => c * f (φ w) with hg
  have hφa : ∀ w : ℂ, AnalyticAt ℂ φ w := fun w => by
    rw [hφ]
    exact analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  have hφd : ∀ w : ℂ, deriv φ w = (R : ℂ) := by
    intro w
    rw [hφ]
    simp
  have hφinj : Function.Injective φ := by
    intro a b hab
    rw [hφ] at hab
    simp only [add_right_inj] at hab
    exact mul_left_cancel₀ hRC hab
  have hga : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) 1) := by
    intro w hw
    have hwn : ‖w‖ ≤ 1 := by rwa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] at hw
    have hmem : φ w ∈ Metric.closedBall s₀ R := by
      have := hφmem (r := 1) hwn
      simpa using this
    exact analyticAt_const.mul ((hfa (φ w) hmem).comp (hφa w))
  have hg0 : g 0 = 1 := by
    rw [hg, hc]
    simp only [hφ, mul_zero, add_zero]
    exact inv_mul_cancel₀ hf0
  have hg0' : g 0 ≠ 0 := by rw [hg0]; exact one_ne_zero
  have hfin : (SetOfZeros 1 g).Finite := finite_SetOfZeros hga hg0'
  have hgB : ∀ w : ℂ, ‖w‖ ≤ 24/25 → ‖g w‖ ≤ B := by
    intro w hw
    rw [hg]
    simp only
    rw [norm_mul, hc, norm_inv]
    rw [inv_mul_le_iff₀ (norm_pos_iff.mpr hf0)]
    calc ‖f (φ w)‖ ≤ B * ‖f s₀‖ := hfB (φ w) (hφmem hw)
      _ = ‖f s₀‖ * B := mul_comm _ _
  have hfnezero : ∀ ρg : ℂ, g ρg = 0 ↔ f (φ ρg) = 0 := by
    intro ρg
    rw [hg]
    simp only
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h hcne
      · exact h
    · intro h
      rw [h, mul_zero]
  set Zg := (finiteSetOfZeros_mono (by norm_num : (22/25 : ℝ) < 1) hfin).toFinset with hZg
  have hZgmem : ∀ ρg : ℂ, ρg ∈ Zg ↔ (‖ρg‖ ≤ 22/25 ∧ f (φ ρg) = 0) := by
    intro ρg
    rw [hZg, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (hfnezero ρg).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (hfnezero ρg).mpr h2⟩
  have hord : ∀ ρg : ℂ, ‖ρg‖ ≤ 1 → analyticOrderNatAt g ρg = analyticOrderNatAt f (φ ρg) := by
    intro ρg hρg
    have hcomp : analyticOrderAt (f ∘ φ) ρg = analyticOrderAt f (φ ρg) :=
      analyticOrderAt_comp_of_deriv_ne_zero (hφa ρg) (by rw [hφd]; exact hRC)
    have hsmul : analyticOrderAt g ρg = analyticOrderAt (f ∘ φ) ρg := by
      have heq : g = (fun _ : ℂ => c) • (f ∘ φ) := by
        funext w
        simp [hg, smul_eq_mul]
      rw [heq, analyticOrderAt_smul analyticAt_const
        (((hfa (φ ρg) (by simpa using hφmem (r := 1) hρg)).comp (hφa ρg)))]
      rw [(analyticAt_const (v := c)).analyticOrderAt_eq_zero.mpr hcne, zero_add]
    rw [analyticOrderNatAt, analyticOrderNatAt, hsmul, hcomp]
  refine ⟨Zg.image φ, ?_, ?_, ?_⟩
  · ext ρ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Set.mem_setOf_eq]
    constructor
    · rintro ⟨ρg, hρg, rfl⟩
      obtain ⟨h1, h2⟩ := (hZgmem ρg).mp hρg
      exact ⟨by simpa using hφmem h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨(ρ - s₀) / (R : ℂ), ?_, ?_⟩
      · rw [hZgmem]
        constructor
        · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
            div_le_iff₀ hR]
          rw [Metric.mem_closedBall, Complex.dist_eq] at h1
          linarith [h1]
        · rw [show φ ((ρ - s₀) / (R:ℂ)) = ρ by rw [hφ]; field_simp; ring]
          exact h2
      · rw [hφ]; field_simp; ring
  · have hcount := ZerosBound (by norm_num) (by norm_num)
      (by norm_num : (22/25:ℝ) < 24/25) (by norm_num) hga hg0 hfin hgB
    rw [Finset.sum_image (fun a _ b _ hab => hφinj hab)]
    have hcongr : ∀ ρg ∈ Zg, (analyticOrderNatAt f (φ ρg) : ℝ) = (analyticOrderNatAt g ρg : ℝ) := by
      intro ρg hρg
      rw [hord ρg (le_trans ((hZgmem ρg).mp hρg).1 (by norm_num))]
    rw [Finset.sum_congr rfl hcongr]
    exact_mod_cast hcount
  · intro s hs hfs
    set w : ℂ := (s - s₀) / (R : ℂ) with hw
    have hφw : φ w = s := by rw [hφ, hw]; field_simp; ring
    have hwn : ‖w‖ ≤ 83/100 := by
      rw [hw, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_le_iff₀ hR]
      rw [Metric.mem_closedBall, Complex.dist_eq] at hs
      linarith [hs]
    have hgw : g w ≠ 0 := by
      rw [hg]
      simp only
      rw [hφw]
      exact mul_ne_zero hcne hfs
    have hunit := logDeriv_partial_fraction_unit hga hg0 hfin hB2 hgB hwn hgw
    have hsR : s ∈ Metric.closedBall s₀ R :=
      Metric.closedBall_subset_closedBall (by nlinarith) hs
    have hld : logDeriv g w = (R : ℂ) * logDeriv f s := by
      have hstep : logDeriv g w = logDeriv (f ∘ φ) w := by
        rw [hg]
        exact logDeriv_const_mul w c hcne
      have hdf : DifferentiableAt ℂ f (φ w) := by
        rw [hφw]
        exact (hfa s hsR).differentiableAt
      rw [hstep, logDeriv_comp hdf (hφa w).differentiableAt, hφw, hφd, mul_comm]
    have hsum : ∑ ρ ∈ Zg.image φ, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)
        = (R : ℂ)⁻¹ * ∑ ρg ∈ Zg, (analyticOrderNatAt g ρg : ℂ) / (w - ρg) := by
      rw [Finset.sum_image (fun a _ b _ hab => hφinj hab), Finset.mul_sum]
      refine Finset.sum_congr rfl fun ρg hρg => ?_
      have h34 : ‖ρg‖ ≤ 22/25 := ((hZgmem ρg).mp hρg).1
      rw [hord ρg (by linarith)]
      have hsub : s - φ ρg = (R : ℂ) * (w - ρg) := by
        rw [← hφw, hφ]
        ring
      rw [hsub]
      rw [div_mul_eq_div_div_swap]
      field_simp
    rw [hsum]
    have hfld : logDeriv f s = (R:ℂ)⁻¹ * logDeriv g w := by
      rw [hld]
      field_simp
    rw [hfld, ← mul_sub, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR]
    rw [div_eq_inv_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hunit (inv_nonneg.mpr hR.le)

end DusartSmoothing.Landau


