-- Prove2me | solution 1 for Arxivcond_mat_0004049.delay_time_density
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T16:11:02.922952+00:00
-- url     : https://prove2.me/submissions/8fc9e193-36e4-4497-bfec-13e500f90fa5

import Theorems.Thm_Arxivcond_mat_0004049_joint_intensity_delay_density
import Theorems.Thm_Arxivcond_mat_0004049_localizedModel_isProbabilityMeasure

open MeasureTheory ProbabilityTheory Set

namespace Arxivcond_mat_0004049

section GammaIntegral
open MeasureTheory

/-- `x ^ (3/2) = x * √x` for `x ≥ 0`. -/
private lemma rpow_three_halves {x : ℝ} (hx : 0 ≤ x) : x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add' hx (by norm_num), Real.rpow_one,
    Real.sqrt_eq_rpow]

/-- The degenerate case `B2 - B1² ≤ 0`: both sides vanish. -/
private lemma eq13_degenerate (N : ℕ) (B1 B2 φ : ℝ) (hs : B2 - B1 ^ 2 ≤ 0) :
    ∫⁻ I, ENNReal.ofReal (eq13Kernel N B1 B2 I φ) = ENNReal.ofReal (eq16Kernel B1 B2 φ) := by
  have hL : ∀ I, eq13Kernel N B1 B2 I φ = 0 := by
    intro I
    simp [eq13Kernel, Real.sqrt_eq_zero'.mpr hs]
  have hR : eq16Kernel B1 B2 φ ≤ 0 := by
    unfold eq16Kernel
    rcases le_or_gt 0 (B2 + φ ^ 2 - 2 * B1 * φ) with hD | hD
    · exact div_nonpos_of_nonpos_of_nonneg hs (by positivity)
    · have h0 : (B2 + φ ^ 2 - 2 * B1 * φ) ^ ((3 : ℝ) / 2) = 0 := by
        rw [Real.rpow_def_of_neg hD,
          show (3 : ℝ) / 2 * Real.pi = Real.pi / 2 + Real.pi by ring, Real.cos_add_pi,
          Real.cos_pi_div_two]
        simp
      simp [h0]
  simp [hL, ENNReal.ofReal_eq_zero.mpr hR]

private lemma eq13_pos (N : ℕ) (hN : 1 ≤ N) (B1 B2 φ : ℝ) (hs : 0 < B2 - B1 ^ 2) :
    ∫⁻ I, ENNReal.ofReal (eq13Kernel N B1 B2 I φ) = ENNReal.ofReal (eq16Kernel B1 B2 φ) := by
  set s := B2 - B1 ^ 2 with hs_def
  set D := B2 + φ ^ 2 - 2 * B1 * φ with hD_def
  have hDs : D = s + (φ - B1) ^ 2 := by rw [hD_def, hs_def]; ring
  have hD : 0 < D := by rw [hDs]; positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set r := (N : ℝ) * D / s with hr_def
  have hr : 0 < r := by positivity
  set C := Real.sqrt ((N : ℝ) ^ 3 / Real.pi) / Real.sqrt s with hC_def
  set f : ℝ → ℝ := fun I => C * (I ^ ((3 : ℝ) / 2 - 1) * Real.exp (-(r * I))) with hf_def
  have hker : ∀ I, 0 < I → eq13Kernel N B1 B2 I φ = f I := by
    intro I hI
    simp only [eq13Kernel, if_pos hI, hf_def, hC_def]
    rw [show (N : ℝ) ^ 3 * I / Real.pi = (N : ℝ) ^ 3 / Real.pi * I by ring,
      Real.sqrt_mul (by positivity), show (3 : ℝ) / 2 - 1 = 1 / 2 by norm_num,
      ← Real.sqrt_eq_rpow]
    have hexp : Real.exp (-(N : ℝ) * I) * Real.exp (-(N : ℝ) * I * (φ - B1) ^ 2 / s) =
        Real.exp (-(r * I)) := by
      rw [← Real.exp_add, hr_def, hDs]
      congr 1
      field_simp
      ring
    calc _ = Real.sqrt ((N : ℝ) ^ 3 / Real.pi) * (Real.sqrt s)⁻¹ * Real.sqrt I *
          (Real.exp (-(N : ℝ) * I) * Real.exp (-(N : ℝ) * I * (φ - B1) ^ 2 / s)) := by ring
      _ = _ := by rw [hexp]; ring
  have hint : ∫ I in Set.Ioi 0, f I = eq16Kernel B1 B2 φ := by
    have hG : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
      rw [show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
        Real.Gamma_one_half_eq]
      ring
    simp only [hf_def]
    rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) hr, hG,
      rpow_three_halves (by positivity)]
    unfold eq16Kernel
    rw [← hD_def, rpow_three_halves hD.le, hC_def, hr_def]
    have hsq : Real.sqrt (1 / ((N : ℝ) * D / s)) =
        Real.sqrt s / (Real.sqrt N * Real.sqrt D) := by
      rw [one_div_div, Real.sqrt_div' _ (by positivity), Real.sqrt_mul hNpos.le]
    have hN3 : Real.sqrt ((N : ℝ) ^ 3 / Real.pi) = N * Real.sqrt N / Real.sqrt Real.pi := by
      rw [Real.sqrt_div' _ Real.pi_pos.le, show (N : ℝ) ^ 3 = N ^ 2 * N by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hNpos.le]
    rw [hsq, hN3]
    have h1 : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
    have h2 : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
    have h3 : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
    have h4 : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have h5 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
    have h6 : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt hNpos.le
    field_simp
    rw [← h5]
    ring_nf
    exact h5
  have hf_int : IntegrableOn f (Set.Ioi 0) := by
    by_contra h
    have h0 := integral_undef h
    rw [hint] at h0
    have : 0 < eq16Kernel B1 B2 φ := by unfold eq16Kernel; rw [← hD_def]; positivity
    linarith
  have hf_nn : ∀ I ∈ Set.Ioi (0 : ℝ), 0 ≤ f I := by
    intro I hI
    exact mul_nonneg (by positivity)
      (mul_nonneg (Real.rpow_nonneg (le_of_lt hI) _) (Real.exp_pos _).le)
  have hlin : (fun I => ENNReal.ofReal (eq13Kernel N B1 B2 I φ)) =
      (Set.Ioi (0 : ℝ)).indicator (fun I => ENNReal.ofReal (f I)) := by
    funext I
    by_cases hI : 0 < I
    · simp [Set.indicator, hI, hker I hI]
    · simp [Set.indicator, hI, eq13Kernel]
  rw [hlin, lintegral_indicator measurableSet_Ioi, ← hint,
    ofReal_integral_eq_lintegral_ofReal hf_int ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall hf_nn))]


private theorem lintegral_eq13Kernel (N : ℕ) (hN : 1 ≤ N) (B1 B2 φ : ℝ) :
    ∫⁻ I, ENNReal.ofReal (eq13Kernel N B1 B2 I φ) = ENNReal.ofReal (eq16Kernel B1 B2 φ) := by
  rcases le_or_gt (B2 - B1 ^ 2) 0 with hs | hs
  · exact eq13_degenerate N B1 B2 φ hs
  · exact eq13_pos N hN B1 B2 φ hs

end GammaIntegral


private lemma measurable_eq13 (N : ℕ) :
    Measurable (fun p : Sample N × (ℝ × ℝ) => ENNReal.ofReal
      (eq13Kernel N (specMoment 1 p.1) (specMoment 2 p.1) p.2.1 p.2.2)) := by
  unfold eq13Kernel specMoment uVec tau
  refine Measurable.ennreal_ofReal (Measurable.ite (measurableSet_lt measurable_const (by fun_prop))
    (by fun_prop) measurable_const)

private theorem delay_time_density_aux (N : ℕ) (hN : 2 ≤ N) (γ : ℝ) (hγ : 0 < γ) :
    (localizedModel N γ).map delayNe =
      (volume : Measure ℝ).withDensity (fun φ =>
        ∫⁻ ω, ENNReal.ofReal (eq16Kernel (specMoment 1 ω) (specMoment 2 ω) φ)
          ∂(localizedModel N γ)) := by
  have := localizedModel_isProbabilityMeasure N γ hγ
  set K : ℝ × ℝ → ENNReal := fun q => ∫⁻ ω, ENNReal.ofReal
    (eq13Kernel N (specMoment 1 ω) (specMoment 2 ω) q.1 q.2) ∂(localizedModel N γ) with hK
  have hk := measurable_eq13 N
  have hKm : Measurable K := hk.lintegral_prod_left'
  have hI : Measurable (intensityNe : Sample N → ℝ) := by unfold intensityNe ampA uVec vVec tau; fun_prop
  have hD : Measurable (delayNe : Sample N → ℝ) := by unfold delayNe ampA uVec vVec tau; fun_prop
  -- integrating the intensity out of the eq. (13) kernel gives the eq. (16) kernel
  have hmarg : ∀ φ, ∫⁻ I, K (I, φ) = ∫⁻ ω, ENNReal.ofReal
      (eq16Kernel (specMoment 1 ω) (specMoment 2 ω) φ) ∂(localizedModel N γ) := by
    intro φ
    simp only [hK]
    rw [lintegral_lintegral_swap (f := fun (I : ℝ) (ω : Sample N) => ENNReal.ofReal
      (eq13Kernel N (specMoment 1 ω) (specMoment 2 ω) I φ))
      (hk.comp (measurable_snd.prodMk (measurable_fst.prodMk measurable_const))).aemeasurable]
    exact lintegral_congr fun ω => lintegral_eq13Kernel N (by omega) _ _ φ
  have hmap : (localizedModel N γ).map delayNe =
      ((localizedModel N γ).map (fun ω => (intensityNe ω, delayNe ω))).map Prod.snd := by
    rw [Measure.map_map measurable_snd (hI.prodMk hD)]; rfl
  rw [hmap, joint_intensity_delay_density N hN γ hγ]
  ext S hS
  rw [Measure.map_apply measurable_snd hS, withDensity_apply _ (measurable_snd hS),
    withDensity_apply _ hS, Measure.volume_eq_prod,
    show Prod.snd ⁻¹' S = (univ : Set ℝ) ×ˢ S by ext; simp, ← Measure.prod_restrict,
    Measure.restrict_univ, lintegral_prod_symm _ hKm.aemeasurable]
  exact lintegral_congr fun φ => hmarg φ

end Arxivcond_mat_0004049

open Arxivcond_mat_0004049 in
theorem solution (N : ℕ) (hN : 2 ≤ N) (γ : ℝ) (hγ : 0 < γ) :
    (localizedModel N γ).map delayNe =
      (volume : Measure ℝ).withDensity (fun φ =>
        ∫⁻ ω, ENNReal.ofReal (eq16Kernel (specMoment 1 ω) (specMoment 2 ω) φ)
          ∂(localizedModel N γ)) :=
  delay_time_density_aux N hN γ hγ
