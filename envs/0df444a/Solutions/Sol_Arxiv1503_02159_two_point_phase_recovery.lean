-- Prove2me | solution 1 for Arxiv1503_02159.two_point_phase_recovery
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-11-25T02:08:05.573455+00:00
-- url     : https://prove2.me/submissions/ae1a7e60-409e-4463-99ca-a4c9618fd5fd

import Definitions.Def_Arxiv1503_02159_Basic

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace Arxiv1503_02159.PhaseRecoveryProof

def wave (k x : ℝ) : ℂ := Complex.exp ((k : ℂ) * (x : ℂ) * Complex.I)

theorem wave_deriv (k x : ℝ) :
    HasDerivAt (wave k) ((k : ℂ) * Complex.I * wave k x) x := by
  unfold wave
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (((hasDerivAt_id x).ofReal_comp.const_mul (k : ℂ)).mul_const Complex.I).cexp

theorem wave_mul_neg (k x : ℝ) : wave k x * wave (-k) x = 1 := by
  unfold wave
  rw [← Complex.exp_add]
  convert Complex.exp_zero using 1
  push_cast
  ring

theorem norm_wave (k x : ℝ) : ‖wave k x‖ = 1 := by
  simp [wave, Complex.norm_exp]

/-- The integrated Schrödinger equation gives the classical free equation
on the open negative half-line. -/
theorem free_second_deriv (v : ℝ → ℝ) (k : ℝ) (ψ : ℝ → ℂ) (r t : ℂ)
    (hv : IsAdmissiblePotential v) (hψ : IsScatteringSolution v k ψ r t)
    (x : ℝ) (hx : x < 0) :
    HasDerivAt (deriv ψ) (-((k : ℂ) ^ 2) * ψ x) x := by
  have hc : Continuous (fun y => -((k : ℂ) ^ 2) * ψ y) :=
    continuous_const.mul hψ.1.continuous
  have heq : ∀ y ∈ Iio (0 : ℝ), deriv ψ y = deriv ψ (-1) +
      ∫ z in (-1 : ℝ)..y, -((k : ℂ) ^ 2) * ψ z := by
    intro y hy
    have hi := hψ.2.1 (-1) y
    have hint : (∫ z in (-1 : ℝ)..y, ((v z : ℂ) - (k : ℂ) ^ 2) * ψ z) =
        ∫ z in (-1 : ℝ)..y, -((k : ℂ) ^ 2) * ψ z := by
      apply intervalIntegral.integral_congr
      intro z hz
      have hz0 : z < 0 := lt_of_le_of_lt hz.2 (max_lt (by norm_num) hy)
      simp only [hv.2.2 z hz0, Complex.ofReal_zero, zero_sub]
    rw [hint] at hi
    linear_combination hi
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable (-1) x)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add (deriv ψ (-1))
  apply hd.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hx] with y hy
  exact heq y hy

/-- Every solution of the free equation on the negative half-line is a fixed
linear combination of the incoming and reflected plane waves. -/
theorem free_wave_representation (v : ℝ → ℝ) (k : ℝ) (ψ : ℝ → ℂ) (r t : ℂ)
    (hv : IsAdmissiblePotential v) (hk : 0 < k) (hψ : IsScatteringSolution v k ψ r t) :
    ∃ A B : ℂ, ∀ x < 0, ψ x = A * wave k x + B * wave (-k) x := by
  let q : ℂ := (k : ℂ) * Complex.I
  have hq : q ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hk)) Complex.I_ne_zero
  have hq2 : q ^ 2 = -(k : ℂ) ^ 2 := by dsimp [q]; ring_nf; simp
  let a : ℝ → ℂ := fun x => (deriv ψ x + q * ψ x) * wave (-k) x
  let b : ℝ → ℂ := fun x => (q * ψ x - deriv ψ x) * wave k x
  have ha : ∀ x < 0, HasDerivAt a 0 x := by
    intro x hx
    have hd := free_second_deriv v k ψ r t hv hψ x hx
    have hf := (hψ.1 x).hasDerivAt
    have he := wave_deriv (-k) x
    convert (hd.add (hf.const_mul q)).mul he using 1 <;>
      first | rfl | (dsimp [a, q]; push_cast; ring_nf; simp)
  have hb : ∀ x < 0, HasDerivAt b 0 x := by
    intro x hx
    have hd := free_second_deriv v k ψ r t hv hψ x hx
    have hf := (hψ.1 x).hasDerivAt
    have he := wave_deriv k x
    convert ((hf.const_mul q).sub hd).mul he using 1 <;>
      first | rfl | (dsimp [b, q]; ring_nf; simp)
  have hac : ∀ x < 0, a x = a (-1) := by
    intro x hx
    exact isOpen_Iio.is_const_of_deriv_eq_zero (convex_Iio (0 : ℝ)).isPreconnected
      (fun y hy => (ha y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (ha y hy).deriv) hx (by norm_num)
  have hbc : ∀ x < 0, b x = b (-1) := by
    intro x hx
    exact isOpen_Iio.is_const_of_deriv_eq_zero (convex_Iio (0 : ℝ)).isPreconnected
      (fun y hy => (hb y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hb y hy).deriv) hx (by norm_num)
  refine ⟨a (-1) / (2 * q), b (-1) / (2 * q), ?_⟩
  intro x hx
  rw [← hac x hx, ← hbc x hx]
  have he : a x * wave k x + b x * wave (-k) x = 2 * q * ψ x := by
    calc
      _ = (deriv ψ x + q * ψ x) * (wave k x * wave (-k) x) +
        (q * ψ x - deriv ψ x) * (wave k x * wave (-k) x) := by dsimp [a,b]; ring
      _ = _ := by rw [wave_mul_neg]; ring
  field_simp
  linear_combination -he

theorem wave_add (k x y : ℝ) : wave k (x + y) = wave k x * wave k y := by
  unfold wave
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A free oscillatory solution cannot have a nonzero component that decays at
negative infinity. A quarter-wavelength shift separates the two components. -/
theorem scattering_left_exact (v : ℝ → ℝ) (k : ℝ) (ψ : ℝ → ℂ) (r t : ℂ)
    (hv : IsAdmissiblePotential v) (hk : 0 < k) (hψ : IsScatteringSolution v k ψ r t) :
    ∀ x < 0, ψ x = wave k x + r * wave (-k) x := by
  obtain ⟨A, B, hrep⟩ := free_wave_representation v k ψ r t hv hk hψ
  let F : ℝ → ℂ := fun x => ψ x - (wave k x + r * wave (-k) x)
  have hF : Tendsto F atBot (𝓝 0) := by
    simpa [F, wave] using hψ.2.2.2.1
  have heq : ∀ x < 0, F x = (A - 1) * wave k x + (B - r) * wave (-k) x := by
    intro x hx
    dsimp [F]
    rw [hrep x hx]
    ring
  let δ : ℝ := Real.pi / (2 * k)
  have hkδ : k * δ = Real.pi / 2 := by
    dsimp [δ]
    field_simp
  have hp : wave k δ = Complex.I := by
    unfold wave
    rw [← Complex.ofReal_mul, hkδ]
    simp [Complex.exp_mul_I]
  have hm : wave (-k) δ = -Complex.I := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    rw [← hp, wave_mul_neg]
    simp [hp]
  have hshift : Tendsto (fun x : ℝ => x + δ) atBot atBot := by
    refine tendsto_atBot.2 ?_
    intro bound
    filter_upwards [eventually_le_atBot (bound - δ)] with x hx
    linarith
  have hlim : Tendsto (fun x => F x - Complex.I * F (x + δ)) atBot (𝓝 0) := by
    simpa using hF.sub (tendsto_const_nhds.mul (hF.comp hshift))
  have hcomb : (fun x => F x - Complex.I * F (x + δ)) =ᶠ[atBot]
      (fun x => (2 : ℂ) * (A - 1) * wave k x) := by
    filter_upwards [eventually_lt_atBot (min (0 : ℝ) (-δ))] with x hx
    have hx0 : x < 0 := lt_of_lt_of_le hx (min_le_left _ _)
    have hxs : x + δ < 0 := by have hb := lt_of_lt_of_le hx (min_le_right _ _); linarith
    rw [heq x hx0, heq (x + δ) hxs, wave_add, wave_add, hp, hm]
    ring_nf
    simp
    ring
  have hnormA := (hlim.congr' hcomb).norm
  simp only [norm_mul, norm_wave, mul_one, norm_zero] at hnormA
  have hzeroA : ‖(2 : ℂ)‖ * ‖A - 1‖ = 0 := tendsto_nhds_unique tendsto_const_nhds hnormA
  have hA : A = 1 := by
    have h := (mul_eq_zero.mp (norm_eq_zero.mp (by simpa only [norm_mul] using hzeroA : ‖(2 : ℂ) * (A - 1)‖ = 0))).resolve_left (by norm_num)
    exact sub_eq_zero.mp h
  have heqB : F =ᶠ[atBot] (fun x => (B - r) * wave (-k) x) := by
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
    simp [heq x hx, hA]
  have hnormB := (hF.congr' heqB).norm
  simp only [norm_mul, norm_wave, mul_one, norm_zero] at hnormB
  have hzeroB : ‖B - r‖ = 0 := tendsto_nhds_unique tendsto_const_nhds hnormB
  have hB : B = r := sub_eq_zero.mp (norm_eq_zero.mp hzeroB)
  intro x hx
  simpa only [hA, hB, one_mul] using hrep x hx

theorem conj_wave (k x : ℝ) : starRingEnd ℂ (wave k x) = wave (-k) x := by
  simp only [wave, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
    Complex.ofReal_neg]
  congr 1
  ring

theorem wave_sq (k x : ℝ) : wave k x * wave k x = wave (2 * k) x := by
  unfold wave
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem wave_re (k x : ℝ) : (wave k x).re = Real.cos (k * x) := by
  unfold wave
  rw [← Complex.ofReal_mul]
  exact Complex.exp_ofReal_mul_I_re (k * x)

theorem wave_im (k x : ℝ) : (wave k x).im = Real.sin (k * x) := by
  unfold wave
  rw [← Complex.ofReal_mul]
  exact Complex.exp_ofReal_mul_I_im (k * x)

/-- The interference term in the measured intensity is a real linear
combination of the two components of the reflection coefficient. -/
theorem intensity_equation (v : ℝ → ℝ) (k : ℝ) (ψ : ℝ → ℂ) (r t : ℂ)
    (hv : IsAdmissiblePotential v) (hk : 0 < k) (hψ : IsScatteringSolution v k ψ r t)
    (x : ℝ) (hx : x < 0) :
    phaselessA ψ x - ‖r‖ ^ 2 =
      2 * (Real.cos (2 * k * x) * r.re + Real.sin (2 * k * x) * r.im) := by
  have hl := scattering_left_exact v k ψ r t hv hk hψ x hx
  have hs (k' : ℝ) : Complex.normSq (wave k' x) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_wave]
    norm_num
  have hcross : (wave k x * starRingEnd ℂ (r * wave (-k) x)).re =
      Real.cos (2 * k * x) * r.re + Real.sin (2 * k * x) * r.im := by
    rw [map_mul, conj_wave, neg_neg]
    have he : wave k x * (starRingEnd ℂ r * wave k x) =
        starRingEnd ℂ r * wave (2 * k) x := by rw [← wave_sq]; ring
    rw [he, Complex.mul_re, wave_re, wave_im]
    simp
    ring
  have hn := congrArg Complex.normSq hl
  rw [Complex.normSq_add, Complex.normSq_mul, hs k, hs (-k), mul_one,
    Complex.normSq_eq_norm_sq r, hcross] at hn
  unfold phaselessA
  rw [Complex.sq_norm, hn]
  ring

end Arxiv1503_02159.PhaseRecoveryProof

open Arxiv1503_02159 Arxiv1503_02159.PhaseRecoveryProof

theorem solution (v : ℝ → ℝ) (hv : IsAdmissiblePotential v)
    (k : ℝ) (hk : 0 < k) (ψ : ℝ → ℂ) (s21 s22 : ℂ) (hψ : IsScatteringSolution v k ψ s21 s22)
    (α : ℝ) (hα : s21 = (‖s21‖ : ℂ) * Complex.exp (α * Complex.I))
    (x1 x2 : ℝ) (hx1 : x1 < 0) (hx2 : x2 < 0)
    (hx12 : ∀ n : ℤ, x1 - x2 ≠ n * (Real.pi / (2 * k))) :
    ‖s21‖ * Real.cos α = (2 * Real.sin (2 * k * (x2 - x1)))⁻¹ *
        (Real.sin (2 * k * x2) * (phaselessA ψ x1 - ‖s21‖ ^ 2)
          - Real.sin (2 * k * x1) * (phaselessA ψ x2 - ‖s21‖ ^ 2)) ∧
    ‖s21‖ * Real.sin α = (2 * Real.sin (2 * k * (x2 - x1)))⁻¹ *
        (-Real.cos (2 * k * x2) * (phaselessA ψ x1 - ‖s21‖ ^ 2)
          + Real.cos (2 * k * x1) * (phaselessA ψ x2 - ‖s21‖ ^ 2)) := by
  have hre : s21.re = ‖s21‖ * Real.cos α := by
    have h := congrArg Complex.re hα
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, zero_mul, sub_zero] using h
  have him : s21.im = ‖s21‖ * Real.sin α := by
    have h := congrArg Complex.im hα
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_im, zero_mul, add_zero] using h
  have h1 := intensity_equation v k ψ s21 s22 hv hk hψ x1 hx1
  have h2 := intensity_equation v k ψ s21 s22 hv hk hψ x2 hx2
  rw [hre, him] at h1 h2
  have hsin : Real.sin (2 * k * (x2 - x1)) ≠ 0 := by
    intro hz
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hz
    apply hx12 (-n)
    push_cast
    field_simp
    nlinarith [hn]
  have hden : 2 * Real.sin (2 * k * (x2 - x1)) ≠ 0 := mul_ne_zero two_ne_zero hsin
  have hdet : Real.sin (2 * k * x2) * Real.cos (2 * k * x1) -
      Real.sin (2 * k * x1) * Real.cos (2 * k * x2) =
      Real.sin (2 * k * (x2 - x1)) := by
    rw [show 2 * k * (x2 - x1) = 2 * k * x2 - 2 * k * x1 by ring, Real.sin_sub]
    ring
  have hnumre : Real.sin (2 * k * x2) * (phaselessA ψ x1 - ‖s21‖ ^ 2) -
      Real.sin (2 * k * x1) * (phaselessA ψ x2 - ‖s21‖ ^ 2) =
      (2 * Real.sin (2 * k * (x2 - x1))) * (‖s21‖ * Real.cos α) := by
    rw [h1, h2, ← hdet]
    ring
  have hnumim : -Real.cos (2 * k * x2) * (phaselessA ψ x1 - ‖s21‖ ^ 2) +
      Real.cos (2 * k * x1) * (phaselessA ψ x2 - ‖s21‖ ^ 2) =
      (2 * Real.sin (2 * k * (x2 - x1))) * (‖s21‖ * Real.sin α) := by
    rw [h1, h2, ← hdet]
    ring
  constructor
  · rw [hnumre, ← mul_assoc, inv_mul_cancel₀ hden, one_mul]
  · rw [hnumim, ← mul_assoc, inv_mul_cancel₀ hden, one_mul]

end
