-- Prove2me | solution 1 for ArtinKP.G2a.hasFDerivAt_block
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:07:00.477521+00:00
-- url     : https://prove2.me/submissions/c6c59648-be93-4fe8-a14e-4d5f72b0b877

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_ArtinKPB017

section
-- module Solutions.Artin.KP.K_Bessel
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-K, file 1: the K-Bessel function

`besselK μ z = ½ ∫_0^∞ t^{μ−1} exp(−(z/2)(t + 1/t)) dt` (`μ : ℂ`, `z : ℝ`; meaningful for `z > 0`),
defined as half the Mellin transform of `besselKer z`.  Mathlib only.

* `besselK_differentiable`: entire in `μ`;
* `besselK_neg`: `K_{−μ} = K_μ`;
* `besselK_ofReal`, `besselKR_pos`: real and positive for real `μ`;
* `norm_besselK_le`: `‖K_μ(z)‖ ≤ K_{Re μ}(z)`;
* `besselKR_le_exp_mul`: `K_μ(z) ≤ e^{−(z−z₀)} K_μ(z₀)` for `z ≥ z₀ > 0`;
* `besselKR_le_gamma`: `K_μ(z) ≤ ½ Γ(|μ|) (z/2)^{−|μ|}` (`μ ≠ 0`);
* `besselKR_le_two_mul`: `K_μ(z) ≤ 2 K_M(z)` for `|μ| ≤ M`;
* `besselKR_le_min`: `K_μ(z) ≤ C min(z^{−|μ|}, z^{−N})` uniformly for `a ≤ |μ| ≤ M ≤ N`;
* `besselK_eq_schlafli`: the Schläfli form `½ (z/2)^{−μ} ∫ t^{μ−1} exp(−t − z²/(4t)) dt`.
-/

namespace ArtinKP.K

open MeasureTheory Set Filter Asymptotics Topology

noncomputable section

theorem besselK_ofReal (μ z : ℝ) : besselK (μ : ℂ) z = (besselKR μ z : ℂ) := by
  unfold besselK besselKR mellin
  rw [Complex.ofReal_mul, ← integral_complex_ofReal]
  congr 1
  · norm_num
  · refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    simp only [smul_eq_mul, Complex.ofReal_mul]
    congr 1
    rw [Complex.ofReal_cpow ht'.le]
    push_cast
    rfl

/-- The Schläfli form: `K_μ(z) = ½ (z/2)^{−μ} ∫_0^∞ t^{μ−1} exp(−t − z²/(4t)) dt` for `z > 0`
(OpenAI's `schlafliBesselK`). -/
theorem besselK_eq_schlafli (μ : ℂ) {z : ℝ} (hz : 0 < z) :
    besselK μ z = (1 / 2 : ℂ) * ((z / 2 : ℝ) : ℂ) ^ (-μ) *
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (μ - 1) * Complex.exp (-(t : ℂ) - (z : ℂ) ^ 2 / (4 * t)) := by
  have h := mellin_comp_mul_left
    (fun t : ℝ => Complex.exp (-(t : ℂ) - (z : ℂ) ^ 2 / (4 * t))) μ (half_pos hz)
  have hfun : (fun t : ℝ => Complex.exp (-((z / 2 * t : ℝ) : ℂ) - (z : ℂ) ^ 2 / (4 * (z / 2 * t : ℝ))))
      = fun t => (besselKer z t : ℂ) := by
    funext t
    unfold besselKer
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    by_cases ht : t = 0
    · subst ht; simp
    · have hzc : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hz.ne'
      have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht
      field_simp
      ring
  rw [hfun] at h
  unfold besselK
  rw [h, smul_eq_mul, mul_assoc]
  rfl

end

end ArtinKP.K
end

section
-- module Solutions.Artin.KP.K_Jacquet
attribute [-instance] _root_.ArtinKP.X.instSigmaFiniteE1Mu1 _root_.ArtinKP.X.instSigmaFiniteXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-K, file 2: the Jacquet integral at a complex place

Additive character: `archChar z = exp(2πi (z + z̄)) = exp(2πi · 2 Re z)` (the trace form `e(Tr z)`
of `ℂ/ℝ`; the goal's `sAddChar` is `exp(−2πi Tr_{F/ℚ}(·))` on fractional parts, whose factor at a
complex place `w` is `archChar (−σ_w ·)`; the Jacquet integral is even in `ν`, so the sign is
immaterial).

`jacquet s ν v = ∫_ℂ (v / (|x|² + v²))^s · archChar(−ν x) dx`. For `Re s > 1`, `v > 0`:

* `jacquet_zero`: `jacquet s 0 v = π/(s−1) · v^{2−s}`;
* `jacquet_eq`: for `ν ≠ 0`,
  `jacquet s ν v = (2π/Γ(s)) · (2π|ν|)^{s−1} · v · K_{s−1}(4π|ν|v)`
  `= (2π^s/Γ(s)) · (2|ν|)^{s−1} · v · K_{s−1}(4π|ν|v)` (`jacquet_eq'`).

The proof is OpenAI's (`OAI.CubicEisenstein.sourceFourierKernel_bessel`, openai/math family 003,
`Eisenstein/HyperbolicSpace.lean`, Apache 2.0; in our port `Definitions.Def_OAIHecke78B005`),
**copied** and restated for `besselK` (importing the bundle would drag B000–B004, ~45k lines).
-/

namespace ArtinKP.K

open MeasureTheory Set Filter
open scoped FourierTransform RealInnerProductSpace

noncomputable section

/-! ## Radial integrals on `ℂ` (copied from OpenAI) -/

lemma sourceFrequency_inner (z freq : ℂ) : inner ℝ z (2*starRingEnd ℂ freq) = 2*(freq*z).re := by
  rw [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply]
  change ((2 * starRingEnd ℂ freq) * starRingEnd ℂ z).re = _
  simp [Complex.mul_re, Complex.mul_im]
  ring

lemma traceIntegral_eq_fourier (f : ℂ → ℂ) (freq : ℂ) :
    (∫ z : ℂ, f z * archChar (-freq*z)) = 𝓕 f (2*starRingEnd ℂ freq) := by
  rw [Real.fourier_eq']
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only
    rw [sourceFrequency_inner]
    change f z *
      Complex.exp (2*Real.pi*Complex.I*((-freq*z)+starRingEnd ℂ (-freq*z))) = _
    simp only [smul_eq_mul]
    rw [mul_comm (f z)]
    congr 1
    congr 1
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring)

lemma hyperbolicKernel_laplace (s : ℂ) (hs : 0 < s.re) (z : ℂ) :
    hyperbolicKernel s z * Complex.Gamma s =
      ∫ t : ℝ in Set.Ioi 0, (t : ℂ)^(s-1) *
        Complex.exp (-((1+‖z‖^2 : ℝ) : ℂ) * t) := by
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs
    (by positivity : 0 < 1+‖z‖^2)
  simp only [neg_mul]
  rw [h]
  congr 1
  rw [hyperbolicKernel, one_div, Complex.inv_cpow_ofReal_nonneg (by positivity),
    Complex.cpow_neg]

lemma source_gaussian_fourier (t : ℝ) (ht : 0 < t) (freq : ℂ) :
    𝓕 (fun z : ℂ => Complex.exp (-(t : ℂ)*‖z‖^2)) (2*starRingEnd ℂ freq) =
      (Real.pi : ℂ)/t * Complex.exp (-(4*Real.pi^2*‖freq‖^2 : ℝ)/t) := by
  rw [fourier_gaussian_innerProductSpace (by simpa using ht)]
  norm_num only [Complex.finrank_real_complex, Nat.cast_ofNat, div_self (by norm_num : (2:ℂ)≠0),
    Complex.cpow_one, norm_mul, Complex.norm_conj, Complex.norm_ofNat]
  congr 2
  push_cast
  ring

lemma norm_gaussianMixture (s freq : ℂ) (t : ℝ) (ht : 0 < t) (z : ℂ) :
    ‖gaussianMixture s freq t z‖ =
      t ^ (s.re-1) * Real.exp (-t) * Real.exp (-t*‖z‖^2) := by
  simp only [gaussianMixture, norm_mul, archChar_norm, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re,
    Complex.norm_exp, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, ← Complex.ofReal_pow, Complex.neg_im, neg_zero, zero_mul, sub_zero]

lemma gaussianMixture_slice_integrable (s freq : ℂ) (t : ℝ) (ht : 0 < t) :
    Integrable (gaussianMixture s freq t) := by
  have hg : Integrable (fun z : ℂ => Complex.exp (-(t : ℂ)*‖z‖^2)) := by
    simpa only [zero_mul, add_zero] using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (by simpa using ht : 0 < (t : ℂ).re) 0 (0 : ℂ)
  apply ((hg.const_mul ((t : ℂ)^(s-1)*Complex.exp (-t))).norm).mono'
  · unfold gaussianMixture
    change AEStronglyMeasurable (fun z : ℂ => (t : ℂ)^(s-1)*Complex.exp (-t)*
      Complex.exp (-(t : ℂ)*‖z‖^2) *
      Complex.exp (2*Real.pi*Complex.I*((-freq*z)+starRingEnd ℂ (-freq*z))))
    fun_prop
  · exact Eventually.of_forall fun z => by
      simp only [gaussianMixture, norm_mul, archChar_norm, mul_one, le_refl]

lemma integral_norm_gaussianMixture (s freq : ℂ) (t : ℝ) (ht : 0 < t) :
    (∫ z : ℂ, ‖gaussianMixture s freq t z‖) =
      Real.pi * (Real.exp (-t)*t^(s.re-2)) := by
  simp_rw [norm_gaussianMixture s freq t ht]
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm ht]
  norm_num only [Complex.finrank_real_complex, Nat.cast_ofNat, div_self (by norm_num : (2:ℝ)≠0),
    Real.rpow_one]
  have hp : t^(s.re-1)/t = t^(s.re-2) := by
    calc
      t^(s.re-1)/t = t^(s.re-1)/t^(1:ℝ) := by rw [Real.rpow_one]
      _ = t^((s.re-1)-1) := (Real.rpow_sub ht _ _).symm
      _ = _ := by congr 1; ring
  calc
    t^(s.re-1)*Real.exp (-t)*(Real.pi/t) = Real.pi*(Real.exp (-t)*(t^(s.re-1)/t)) := by ring
    _ = _ := by rw [hp]

theorem gaussianMixture_integrable (s freq : ℂ) (hs : 1 < s.re) :
    Integrable (fun p : ℝ × ℂ => gaussianMixture s freq p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℂ => gaussianMixture s freq p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
    unfold gaussianMixture
    change AEStronglyMeasurable (fun p : ℝ × ℂ =>
      (p.1 : ℂ)^(s-1)*Complex.exp (-p.1)*Complex.exp (-(p.1 : ℂ)*‖p.2‖^2)*
      Complex.exp (2*Real.pi*Complex.I*((-freq*p.2)+starRingEnd ℂ (-freq*p.2)))) _
    fun_prop
  apply (integrable_prod_iff hmeas).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact gaussianMixture_slice_integrable s freq t ht
  · have hgamma := (Real.GammaIntegral_convergent (by linarith : 0 < s.re-1)).const_mul Real.pi
    apply hgamma.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [integral_norm_gaussianMixture s freq t ht]
    congr 2
    ring_nf

lemma gaussianMixture_laplace_form (s freq : ℂ) (t : ℝ) (z : ℂ) :
    gaussianMixture s freq t z =
      ((t : ℂ)^(s-1) * Complex.exp (-((1+‖z‖^2 : ℝ) : ℂ)*t)) *
        archChar (-freq*z) := by
  have he : Complex.exp (-(t : ℂ))*Complex.exp (-(t : ℂ)*‖z‖^2) =
      Complex.exp (-((1+‖z‖^2 : ℝ) : ℂ)*t) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = (t : ℂ)^(s-1) * (Complex.exp (-(t : ℂ))*Complex.exp (-(t : ℂ)*‖z‖^2)) *
        archChar (-freq*z) := by unfold gaussianMixture; ring
    _ = _ := by rw [he]

lemma integral_gaussianMixture_t (s freq : ℂ) (hs : 0 < s.re) (z : ℂ) :
    (∫ t : ℝ in Set.Ioi 0, gaussianMixture s freq t z) =
      (hyperbolicKernel s z * Complex.Gamma s)*archChar (-freq*z) := by
  simp_rw [gaussianMixture_laplace_form]
  rw [integral_mul_const, ← hyperbolicKernel_laplace s hs z]

lemma integral_gaussianMixture_z (s freq : ℂ) (t : ℝ) (ht : 0 < t) :
    (∫ z : ℂ, gaussianMixture s freq t z) =
      (Real.pi : ℂ) * ((t : ℂ)^(s-2) *
        Complex.exp (-(t : ℂ) - (4*Real.pi^2*‖freq‖^2 : ℝ)/t)) := by
  have hfac : (fun z : ℂ => gaussianMixture s freq t z) =
      (fun z : ℂ => ((t : ℂ)^(s-1)*Complex.exp (-t))*
        (Complex.exp (-(t : ℂ)*‖z‖^2)*archChar (-freq*z))) := by
    funext z
    unfold gaussianMixture
    ring
  rw [hfac, integral_const_mul, traceIntegral_eq_fourier, source_gaussian_fourier t ht freq]
  have hp : (t : ℂ)^(s-1)/(t : ℂ) = (t : ℂ)^(s-2) := by
    calc
      _ = (t : ℂ)^(s-1)/(t : ℂ)^(1 : ℂ) := by rw [Complex.cpow_one]
      _ = (t : ℂ)^((s-1)-1) := (Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr ht.ne')).symm
      _ = _ := by congr 1; ring
  calc
    _ = (Real.pi : ℂ)*(((t : ℂ)^(s-1)/t)*
        (Complex.exp (-(t : ℂ))*Complex.exp (-(4*Real.pi^2*‖freq‖^2 : ℝ)/t))) := by ring
    _ = _ := by rw [hp, ← Complex.exp_add]; congr 2; ring_nf

theorem sourceFourierKernel_gamma (s freq : ℂ) (hs : 1 < s.re) :
    sourceFourierKernel s freq * Complex.Gamma s =
      (Real.pi : ℂ) * ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ)^(s-2) * Complex.exp (-(t : ℂ) - (4*Real.pi^2*‖freq‖^2 : ℝ)/t) := by
  have hmix := gaussianMixture_integrable s freq hs
  calc
    _ = ∫ z : ℂ, (hyperbolicKernel s z * Complex.Gamma s)*
        archChar (-freq*z) := by
      rw [sourceFourierKernel, ← integral_mul_const]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by ring
    _ = ∫ z : ℂ, ∫ t : ℝ in Set.Ioi 0, gaussianMixture s freq t z := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => (integral_gaussianMixture_t s freq (by linarith) z).symm
    _ = ∫ t : ℝ in Set.Ioi 0, ∫ z : ℂ, gaussianMixture s freq t z :=
      (integral_integral_swap hmix).symm
    _ = _ := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact integral_gaussianMixture_z s freq t ht

/-! ## The Bessel form (ours, for `besselK`) -/

/-- `∫ (1+|z|²)^{−s} e(−Tr(freq z)) dz = (2π/Γ(s)) (2π|freq|)^{s−1} K_{s−1}(4π|freq|)`. -/
theorem sourceFourierKernel_bessel (s freq : ℂ) (hs : 1 < s.re) (hf : freq ≠ 0) :
    sourceFourierKernel s freq =
      (2*Real.pi : ℂ)/Complex.Gamma s * ((2*Real.pi*‖freq‖ : ℝ) : ℂ)^(s-1) *
        besselK (s-1) (4*Real.pi*‖freq‖) := by
  have hg := Complex.Gamma_ne_zero_of_re_pos (show 0 < s.re by linarith)
  have hz : 0 < 4*Real.pi*‖freq‖ := by
    have := norm_pos_iff.2 hf
    positivity
  have hz2 : (4*Real.pi*‖freq‖)/2 = 2*Real.pi*‖freq‖ := by ring
  have hzc : ((2*Real.pi*‖freq‖ : ℝ) : ℂ) ≠ 0 := by
    rw [← hz2]; exact Complex.ofReal_ne_zero.2 (half_pos hz).ne'
  have hp : ((2*Real.pi*‖freq‖ : ℝ) : ℂ)^(s-1) * ((2*Real.pi*‖freq‖ : ℝ) : ℂ)^(-(s-1)) = 1 := by
    rw [← Complex.cpow_add _ _ hzc, add_neg_cancel, Complex.cpow_zero]
  have hK := besselK_eq_schlafli (s-1) hz
  rw [hz2] at hK
  have hint : (∫ t : ℝ in Set.Ioi 0,
        (t : ℂ)^(s-2) * Complex.exp (-(t : ℂ) - (4*Real.pi^2*‖freq‖^2 : ℝ)/t)) =
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1 - 1) *
        Complex.exp (-(t : ℂ) - ((4*Real.pi*‖freq‖ : ℝ) : ℂ) ^ 2 / (4 * t)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    rw [show s-2=(s-1)-1 by ring]
    apply congrArg (fun w : ℂ => (t : ℂ)^((s-1)-1)*Complex.exp w)
    push_cast
    ring
  have hG := sourceFourierKernel_gamma s freq hs
  rw [hint] at hG
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hg, hG, hK]
  linear_combination (-(Real.pi : ℂ) * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1 - 1) *
        Complex.exp (-(t : ℂ) - ((4*Real.pi*‖freq‖ : ℝ) : ℂ) ^ 2 / (4 * t))) * hp

lemma traceIntegral_scale (v : ℝ) (hv : 0 < v) (s freq : ℂ) :
    (∫ z : ℂ,hyperbolicKernel s (z/(v:ℂ))*archChar (-freq*z))=
      (v:ℂ)^2*sourceFourierKernel s (freq*v) := by
  have heq (z : ℂ) : hyperbolicKernel s (z/(v:ℂ))*archChar (-freq*z)=
      (fun w : ℂ => hyperbolicKernel s w*archChar (-(freq*v)*w)) (v⁻¹ • z) := by
    simp only [Complex.real_smul,Complex.ofReal_inv]
    congr 2
    · ring
    · field_simp [Complex.ofReal_ne_zero.mpr hv.ne']
  simp_rw [heq]
  have h := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure ℂ)
    (fun w : ℂ => hyperbolicKernel s w*archChar (-(freq*v)*w)) hv.le
  simpa only [Complex.finrank_real_complex,Complex.real_smul,Complex.ofReal_pow,sourceFourierKernel] using h

/-! ## The Jacquet integral -/

lemma height_cpow (s : ℂ) {v : ℝ} (hv : 0 < v) (x : ℂ) :
    ((v / (‖x‖ ^ 2 + v ^ 2) : ℝ) : ℂ) ^ s = (v : ℂ) ^ (-s) * hyperbolicKernel s (x / (v : ℂ)) := by
  unfold hyperbolicKernel
  have h1 : (v / (‖x‖ ^ 2 + v ^ 2) : ℝ) = v⁻¹ * (1 + ‖x / (v : ℂ)‖ ^ 2)⁻¹ := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hv.le]
    field_simp
    ring
  have hpos : (0 : ℝ) < 1 + ‖x / (v : ℂ)‖ ^ 2 := by positivity
  rw [h1, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (inv_nonneg.2 hv.le)
    (inv_nonneg.2 hpos.le), Complex.ofReal_inv, Complex.ofReal_inv,
    Complex.inv_cpow_ofReal_nonneg hv.le, Complex.inv_cpow_ofReal_nonneg hpos.le,
    Complex.cpow_neg, Complex.cpow_neg]

theorem jacquet_eq_sourceFourierKernel (s ν : ℂ) {v : ℝ} (hv : 0 < v) :
    jacquet s ν v = (v : ℂ) ^ (2 - s) * sourceFourierKernel s (ν * v) := by
  unfold jacquet
  simp_rw [height_cpow s hv, mul_assoc]
  rw [integral_const_mul, traceIntegral_scale v hv s ν, ← mul_assoc]
  congr 1
  rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hv.ne')]
  congr 1
  push_cast; ring

/-- The Whittaker function: for `ν ≠ 0`,
`∫_ℂ (v/(|x|²+v²))^s e(−Tr(νx)) dx = (2π/Γ(s)) (2π|ν|)^{s−1} · v · K_{s−1}(4π|ν|v)`. -/
theorem jacquet_eq (s : ℂ) (hs : 1 < s.re) {ν : ℂ} (hν : ν ≠ 0) {v : ℝ} (hv : 0 < v) :
    jacquet s ν v = (2 * Real.pi : ℂ) / Complex.Gamma s * ((2 * Real.pi * ‖ν‖ : ℝ) : ℂ) ^ (s - 1) *
      (v : ℂ) * besselK (s - 1) (4 * Real.pi * ‖ν‖ * v) := by
  have hνv : ν * (v : ℂ) ≠ 0 := mul_ne_zero hν (Complex.ofReal_ne_zero.2 hv.ne')
  have hn : ‖ν * (v : ℂ)‖ = ‖ν‖ * v := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hv.le]
  have hvc : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hv.ne'
  rw [jacquet_eq_sourceFourierKernel s ν hv, sourceFourierKernel_bessel s _ hs hνv, hn]
  have h1 : ((2 * Real.pi * (‖ν‖ * v) : ℝ) : ℂ) ^ (s - 1) =
      ((2 * Real.pi * ‖ν‖ : ℝ) : ℂ) ^ (s - 1) * (v : ℂ) ^ (s - 1) := by
    rw [← mul_assoc, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) hv.le]
  have h2 : (v : ℂ) ^ (2 - s) * (v : ℂ) ^ (s - 1) = (v : ℂ) := by
    rw [← Complex.cpow_add _ _ hvc, show 2 - s + (s - 1) = 1 by ring, Complex.cpow_one]
  rw [h1, show 4 * Real.pi * (‖ν‖ * v) = 4 * Real.pi * ‖ν‖ * v by ring]
  linear_combination ((2 * Real.pi : ℂ) / Complex.Gamma s * ((2 * Real.pi * ‖ν‖ : ℝ) : ℂ) ^ (s - 1) *
    besselK (s - 1) (4 * Real.pi * ‖ν‖ * v)) * h2

/-! ## Holomorphy in `s` -/

end

end ArtinKP.K
end

section
-- module Solutions.Artin.T12.L3X_V
/-! # L3X_V: the radial profile `V` of (5.21) and its Mellin transform

* `Vprof w₀ 𝔪 k κ u`: the sheet integral over `X_u` of `1_{y_f = 0} ∏_w κ(|y_w|_w)`.
* `Vprof_eq`: `V(u) = (2π)^{|W|} ∫_{x' ∈ ℝ^{W∖w₀}} κ(e^{log u − Σx'}) ∏_{w'} κ(e^{x'_{w'}})`.
* `Vprof_mellin`: measurability and `V̂(s) = (2π)^{|W|} cκ^{|W|} (Aκ^{|W|})^s (Γ(s+5/6)Γ(s+7/6))^{|W|}`
  for `Re s > −5/6`, from `κ̂(s) = cκ Aκ^s Γ(s+5/6)Γ(s+7/6)` (Fubini; `κ ≥ 0`).
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-! ### The exponential substitution in the Mellin transform -/

theorem cpow_exp_eq (a : ℝ) (s : ℂ) :
    ((Real.exp a : ℝ) : ℂ) * ((Real.exp a : ℝ) : ℂ) ^ (s - 1) = Complex.exp (s * a) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos a).ne'),
    ← Complex.ofReal_log (Real.exp_pos a).le, Real.log_exp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1; ring

theorem mellin_eq_integral_exp (f : ℝ → ℂ) (s : ℂ) :
    mellin f s = ∫ a : ℝ, Complex.exp (s * a) * f (Real.exp a) := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t)
  rw [Set.image_univ, Real.range_exp, Measure.restrict_univ] at h
  rw [mellin, h]
  congr 1; funext a
  rw [abs_of_pos (Real.exp_pos a), smul_eq_mul, Complex.real_smul, ← mul_assoc, cpow_exp_eq]

theorem mellinConvergent_iff_exp (f : ℝ → ℂ) (s : ℂ) :
    MellinConvergent f s ↔ Integrable (fun a : ℝ => Complex.exp (s * a) * f (Real.exp a)) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t)
  rw [Set.image_univ, Real.range_exp, integrableOn_univ] at h
  rw [MellinConvergent, h]
  refine integrable_congr (Filter.Eventually.of_forall fun a => ?_)
  simp only
  rw [abs_of_pos (Real.exp_pos a), smul_eq_mul, Complex.real_smul, ← mul_assoc, cpow_exp_eq]

/-! ### The Mellin transform of `V` -/

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.T12.L3J_Kappa
/-! # L3J_Kappa: the κ-clauses of the corrected KP cut are satisfiable

`κ₀(t) = ∫ g_{5/6}(log t − y) g_{7/6}(y) dy`, with `g_a(b) = exp(a b − e^b)`, is the Mellin
convolution of `t^{5/6} e^{-t}` and `t^{7/6} e^{-t}`. So `mellin κ₀ s = Γ(s+5/6) Γ(s+7/6)` for
`Re s > −5/6`, and `κ₀(t) ≤ C_N min(t^α, t^{-N})` for every `0 < α ≤ 5/6` and every `N > 0`.
It is the archimedean Whittaker profile `t K_{1/3}(2√t)` of (5.7)/(5.11), up to normalization. -/

namespace ArtinPrimitiveRoots.L3J

open MeasureTheory Set

noncomputable section

theorem gA_pos (a b : ℝ) : 0 < gA a b := Real.exp_pos _

theorem continuous_gA (a : ℝ) : Continuous (gA a) := by
  unfold gA; fun_prop

/-- `exp(s b) g_a(b) = exp((s + a) b) exp(−e^b)`. -/
theorem cexp_mul_gA (s : ℂ) (a b : ℝ) :
    Complex.exp (s * b) * (gA a b : ℂ) =
      Complex.exp ((s + a) * b) * ((Real.exp (-Real.exp b) : ℝ) : ℂ) := by
  unfold gA
  rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- `Γ(c)` in exponential coordinates. -/
theorem gamma_exp {c : ℂ} (hc : 0 < c.re) :
    Integrable (fun b : ℝ => Complex.exp (c * b) * ((Real.exp (-Real.exp b) : ℝ) : ℂ)) ∧
    ∫ b : ℝ, Complex.exp (c * b) * ((Real.exp (-Real.exp b) : ℝ) : ℂ) = Complex.Gamma c := by
  have hm : MellinConvergent (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) c := by
    unfold MellinConvergent
    refine (Complex.GammaIntegral_convergent hc).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [smul_eq_mul, Complex.ofReal_exp, Complex.ofReal_neg]
    ring
  refine ⟨(L3X.mellinConvergent_iff_exp _ c).1 hm, ?_⟩
  rw [Complex.Gamma_eq_integral hc, Complex.GammaIntegral_eq_mellin, L3X.mellin_eq_integral_exp]

theorem integrable_cexp_gA {s : ℂ} {a : ℝ} (h : 0 < s.re + a) :
    Integrable (fun b : ℝ => Complex.exp (s * b) * (gA a b : ℂ)) := by
  have := (gamma_exp (c := s + a) (by simpa using h)).1
  simpa only [cexp_mul_gA] using this

theorem integrable_gA {a : ℝ} (ha : 0 < a) : Integrable (gA a) := by
  have h := (integrable_cexp_gA (s := 0) (a := a) (by simpa using ha)).norm
  refine h.congr (Filter.Eventually.of_forall fun b => ?_)
  simp only [zero_mul, Complex.exp_zero, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (gA_pos a b).le]

end

end ArtinPrimitiveRoots.L3J
end

section
-- module Solutions.Artin.KP.K_Kappa
/-! # WP-K, file 3: the profile `κ`

* `cc a b x = ∫ g_a(x−y) g_b(y) dy` (`g_a(u) = exp(a u − e^u)`, `L3J.gA`): the Mellin convolution of
  `t^a e^{−t}` and `t^b e^{−t}` in the variable `x = log t`; `L3J.kappa0 (e^x) = cc (5/6) (7/6) x`.
  `hasDerivAt_cc`: `cc a b ' = a · cc a b − cc (a+1) b`; `contDiff_cc`: smooth;
  `cc_bound`: `cc a b x ≤ C min(e^{αx}, e^{−Nx})` for `a ≠ b`, `0 < α ≤ min a b`.
* `kappa0_eq_bessel`: `κ₀(t) = 2 t K_{1/3}(2√t)`.
* `kappaB c t = t · K_{1/3}(c √t)` (`t > 0`; `0` otherwise) `= (2/c²) κ₀(c² t/4)`;
  `kappaB_clauses`: all `κ`-clauses of the frozen goal with `cκ = 2/c²`, `Aκ = (c²/4)⁻¹ = 4/c²`
  (for `c = 4π`: `cκ = 1/(8π²)`, `Aκ = 1/(4π²)`).
* `kappaB_contDiff`, `kappaB_iteratedDeriv_bound`, `kappaB_iteratedDeriv_bound_shift`,
  `kappaB_ofReal_iteratedDeriv_bound_shift`: `s ↦ κ(e^{x+s})` is smooth and its derivatives of
  order `≤ 2` are `≤ C min(e^{αx}, e^{−Nx})`, `0 < α ≤ 5/6`, any `N > 0`.
-/

namespace ArtinKP.K

open MeasureTheory Set Filter
open ArtinPrimitiveRoots.L3J (gA kappa0 gA_pos continuous_gA integrable_gA)

noncomputable section

/-! ## The functions `g_a` -/

theorem gA_le {a : ℝ} (ha : 0 < a) (b : ℝ) : gA a b ≤ Real.exp (a * Real.log a - a) := by
  unfold gA
  refine Real.exp_le_exp.2 ?_
  have h := Real.add_one_le_exp (b - Real.log a)
  have he : Real.exp (b - Real.log a) = Real.exp b / a := by rw [Real.exp_sub, Real.exp_log ha]
  rw [he, le_div_iff₀ ha] at h
  have : (b - Real.log a + 1) * a = a * b - a * Real.log a + a := by ring
  linarith

theorem exp_mul_gA (a b : ℝ) : Real.exp b * gA a b = gA (a + 1) b := by
  unfold gA
  rw [← Real.exp_add]
  congr 1; ring

theorem hasDerivAt_gA (a b : ℝ) : HasDerivAt (gA a) (a * gA a b - gA (a + 1) b) b := by
  have h := (((hasDerivAt_id b).const_mul a).sub (Real.hasDerivAt_exp b)).exp
  have e : a * gA a b - gA (a + 1) b = Real.exp (a * id b - Real.exp b) * (a * 1 - Real.exp b) := by
    rw [← exp_mul_gA]; unfold gA; simp only [id]; ring
  rw [e]
  exact h

/-! ## The family `cc a b` -/

theorem kappa0_eq_cc (t : ℝ) : kappa0 t = cc (5 / 6) (7 / 6) (Real.log t) := rfl

theorem kappa0_exp (x : ℝ) : kappa0 (Real.exp x) = cc (5 / 6) (7 / 6) x := by
  rw [kappa0_eq_cc, Real.log_exp]

theorem integrable_cc_integrand {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    Integrable fun y => gA a (x - y) * gA b y := by
  refine ((integrable_gA hb).const_mul (Real.exp (a * Real.log a - a))).mono' ?_
    (Eventually.of_forall fun y => ?_)
  · exact (((continuous_gA a).comp (continuous_const.sub continuous_id)).mul
      (continuous_gA b)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (mul_pos (gA_pos _ _) (gA_pos _ _)).le]
    exact mul_le_mul_of_nonneg_right (gA_le ha _) (gA_pos _ _).le

/-- `cc a b ' = a · cc a b − cc (a+1) b`. -/
theorem hasDerivAt_cc {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    HasDerivAt (cc a b) (a * cc a b x - cc (a + 1) b x) x := by
  have ha1 : 0 < a + 1 := by linarith
  set S : ℝ := Real.exp (a * Real.log a - a) with hS
  set S1 : ℝ := Real.exp ((a + 1) * Real.log (a + 1) - (a + 1)) with hS1
  have hF' : ∀ x : ℝ, (fun y => (a * gA a (x - y) - gA (a + 1) (x - y)) * gA b y) =
      fun y => a * (gA a (x - y) * gA b y) - gA (a + 1) (x - y) * gA b y := by
    intro x; funext y; ring
  have hint : ∀ x : ℝ, Integrable fun y => (a * gA a (x - y) - gA (a + 1) (x - y)) * gA b y := by
    intro x
    rw [hF']
    exact ((integrable_cc_integrand ha hb x).const_mul a).sub (integrable_cc_integrand ha1 hb x)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure ℝ))
    (F := fun x y => gA a (x - y) * gA b y)
    (F' := fun x y => (a * gA a (x - y) - gA (a + 1) (x - y)) * gA b y)
    (x₀ := x) (s := univ) (bound := fun y => (a * S + S1) * gA b y) univ_mem
    (Eventually.of_forall fun x => (integrable_cc_integrand ha hb x).aestronglyMeasurable)
    (integrable_cc_integrand ha hb x)
    (hint x).aestronglyMeasurable
    (Eventually.of_forall fun y x _ => by
      rw [norm_mul, Real.norm_of_nonneg (gA_pos b y).le]
      refine mul_le_mul_of_nonneg_right ?_ (gA_pos b y).le
      rw [Real.norm_eq_abs, abs_le]
      have h1 := mul_le_mul_of_nonneg_left (gA_le ha (x - y)) ha.le
      have h2 := gA_le ha1 (x - y)
      have p1 := mul_pos ha (gA_pos a (x - y))
      have p2 := gA_pos (a + 1) (x - y)
      have q1 : 0 < a * S := mul_pos ha (Real.exp_pos _)
      have q2 : 0 < S1 := Real.exp_pos _
      constructor <;> linarith)
    ((integrable_gA hb).const_mul _)
    (Eventually.of_forall fun y x _ => by
      have := ((hasDerivAt_gA a (x - y)).comp_sub_const x y).mul_const (gA b y)
      exact this)
  have h := key.2
  have e : ∫ y, (a * gA a (x - y) - gA (a + 1) (x - y)) * gA b y =
      a * cc a b x - cc (a + 1) b x := by
    rw [hF', integral_sub ((integrable_cc_integrand ha hb x).const_mul a)
      (integrable_cc_integrand ha1 hb x), integral_const_mul]
    rfl
  rw [e] at h
  exact h

/-! ## Bounds for `cc a b` -/

theorem gA_mul_eq' (a b x y : ℝ) :
    gA a (x - y) * gA b y =
      Real.exp (a * x) * Real.exp ((b - a) * y - Real.exp (x - y) - Real.exp y) := by
  unfold gA
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1; ring

/-! ## `κ₀` is a K-Bessel function -/

/-- `K_μ(z) = ½ ∫_ℝ e^{μ a} exp(−(z/2)(e^a + e^{−a})) da`. -/
theorem besselKR_eq_integral_exp (μ z : ℝ) :
    besselKR μ z = 1 / 2 * ∫ a : ℝ, Real.exp (μ * a) * besselKer z (Real.exp a) := by
  have h := besselK_ofReal μ z
  unfold besselK at h
  rw [ArtinPrimitiveRoots.L3X.mellin_eq_integral_exp] at h
  have e : (∫ a : ℝ, Complex.exp ((μ : ℂ) * a) * (besselKer z (Real.exp a) : ℂ)) =
      ((∫ a : ℝ, Real.exp (μ * a) * besselKer z (Real.exp a) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    push_cast
    rfl
  rw [e] at h
  have h' : ((1 / 2 * ∫ a : ℝ, Real.exp (μ * a) * besselKer z (Real.exp a) : ℝ) : ℂ) =
      (besselKR μ z : ℂ) := by
    rw [← h]; push_cast; ring
  exact_mod_cast h'.symm

/-- `κ₀(e^x) = 2 e^x K_{1/3}(2 e^{x/2})`. -/
theorem kappa0_exp_eq_bessel (x : ℝ) :
    kappa0 (Real.exp x) = 2 * Real.exp x * besselKR (1 / 3) (2 * Real.exp (x / 2)) := by
  rw [besselKR_eq_integral_exp,
    ← integral_sub_right_eq_self
      (fun a => Real.exp (1 / 3 * a) * besselKer (2 * Real.exp (x / 2)) (Real.exp a)) (x / 2),
    kappa0_exp]
  unfold cc
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [gA_mul_eq']
  have e1 : Real.exp (x / 2) * Real.exp (y - x / 2) = Real.exp y := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (x / 2) * (Real.exp (y - x / 2))⁻¹ = Real.exp (x - y) := by
    rw [← Real.exp_neg, ← Real.exp_add]; congr 1; ring
  have hk : besselKer (2 * Real.exp (x / 2)) (Real.exp (y - x / 2)) =
      Real.exp (-(Real.exp y + Real.exp (x - y))) := by
    unfold besselKer
    congr 1
    rw [← e1, ← e2]; ring
  rw [hk, ← Real.exp_add, ← Real.exp_add]
  have e3 : Real.exp (5 / 6 * x + ((7 / 6 - 5 / 6) * y - Real.exp (x - y) - Real.exp y)) =
      Real.exp x * Real.exp (1 / 3 * (y - x / 2) + -(Real.exp y + Real.exp (x - y))) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e3]; ring

/-! ## The Bessel profile `κ(t) = t K_{1/3}(c√t)` -/

/-! ## Smoothness and derivative bounds in the logarithmic variable -/

end

end ArtinKP.K
end

section
-- module Solutions.Artin.KP.G2a_Bessel
/-! # WP-G2a, file 10: the `v`-derivative of the Jacquet integral at `s = 4/3`

* `cc_shift`: `cc (a+c) (b+c) x = e^{cx}·cc a b x`; **`zK_eq_cc`**: `z·K_{1/3}(z) = cc (1/3) (2/3) (2 log (z/2))`
  (the lemma "of the type `kappa0_eq_bessel`" that WP-K left open; MATH3 §5.2 (ii)).
* `jacquet_eq_cc`, **`hasDerivAt_jacquet`**: `v ↦ jacquet (4/3) a v` is differentiable on `v > 0`
  with derivative `jd a v` (from `K.hasDerivAt_cc`).
* `grid_decay`: the uniform bound used for both the function and its derivative;
  **`jd_bound`**: `|a|^{2/3}(1+|a|)^p·|jd a v| ≤ K (1+|a|)^{-4}` for `v` in a compact of `(0, ∞)`.
-/

open scoped ComplexConjugate Topology
open MeasureTheory Set NumberField Filter

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.K ArtinKP.B ArtinKP.RF ArtinPrimitiveRoots

noncomputable section

theorem cc_shift (a b c x : ℝ) : cc (a + c) (b + c) x = Real.exp (c * x) * cc a b x := by
  unfold cc
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [L3J.gA]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- **`z·K_{1/3}(z) = cc (1/3) (2/3) (2 log (z/2))`.** -/
theorem zK_eq_cc {z : ℝ} (hz : 0 < z) :
    z * besselKR (1 / 3) z = cc (1 / 3) (2 / 3) (2 * Real.log (z / 2)) := by
  set x : ℝ := 2 * Real.log (z / 2) with hx
  have hz2 : 0 < z / 2 := by positivity
  have e1 : Real.exp (x / 2) = z / 2 := by
    rw [hx, mul_div_cancel_left₀ _ (two_ne_zero), Real.exp_log hz2]
  have e2 : Real.exp x = (z / 2) ^ 2 := by
    rw [hx, show 2 * Real.log (z / 2) = Real.log (z / 2) + Real.log (z / 2) by ring, Real.exp_add,
      Real.exp_log hz2]
    ring
  have h1 := kappa0_exp_eq_bessel x
  rw [kappa0_exp, show (5 / 6 : ℝ) = 1 / 3 + 1 / 2 by norm_num,
    show (7 / 6 : ℝ) = 2 / 3 + 1 / 2 by norm_num, cc_shift, e2, e1,
    show (1 / 2 : ℝ) * x = x / 2 by ring, e1, show 2 * (z / 2) = z by ring] at h1
  have : z / 2 * cc (1 / 3) (2 / 3) x = z / 2 * (z * besselKR (1 / 3) z) := by
    rw [h1]; ring
  exact (mul_left_cancel₀ hz2.ne' this).symm

theorem jacquet_eq_cc {a : ℂ} (ha : a ≠ 0) {v : ℝ} (hv : 0 < v) :
    jacquet (4 / 3) a v = c1 * ((jr ‖a‖ v : ℝ) : ℂ) := by
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hz : 0 < 4 * Real.pi * ‖a‖ * v := by positivity
  have h := zK_eq_cc hz
  rw [show 4 * Real.pi * ‖a‖ * v / 2 = 2 * Real.pi * ‖a‖ * v by ring] at h
  have key : ‖a‖ ^ (1 / 3 : ℝ) = ‖a‖ ^ (-(2 / 3 : ℝ)) * ‖a‖ := by
    conv_rhs => rw [← Real.rpow_one ‖a‖, ← Real.rpow_mul hn.le, ← Real.rpow_add hn]
    norm_num
  rw [jacquet_eq (4 / 3) (by norm_num) ha hv,
    show (4 / 3 : ℂ) - 1 = ((1 / 3 : ℝ) : ℂ) by push_cast; norm_num, besselK_ofReal,
    ← Complex.ofReal_cpow (by positivity), Real.mul_rpow (by positivity) hn.le, key, c1, jr, ← h]
  have hnC : (‖a‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

theorem hasDerivAt_jacquet {a : ℂ} (ha : a ≠ 0) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun t : ℝ => jacquet (4 / 3) a t) (jd a v) v := by
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hc : 0 < 2 * Real.pi * ‖a‖ := by positivity
  have h1 : HasDerivAt (fun t : ℝ => 2 * Real.log (2 * Real.pi * ‖a‖ * t)) (2 / v) v := by
    have h := (((hasDerivAt_id' v).const_mul (2 * Real.pi * ‖a‖)).log
      (mul_pos hc hv).ne').const_mul 2
    exact h.congr_deriv (by field_simp)
  have h2 := (hasDerivAt_cc (a := 1 / 3) (b := 2 / 3) (by norm_num) (by norm_num)
    (2 * Real.log (2 * Real.pi * ‖a‖ * v))).comp v h1
  have h3 : HasDerivAt (fun t : ℝ => jr ‖a‖ t) (‖a‖ ^ (-(2 / 3 : ℝ)) *
      ((1 / 3 * cc (1 / 3) (2 / 3) (2 * Real.log (2 * Real.pi * ‖a‖ * v))
        - cc (1 / 3 + 1) (2 / 3) (2 * Real.log (2 * Real.pi * ‖a‖ * v))) * (2 / v))) v :=
    h2.const_mul _
  have h4 := (h3.ofReal_comp).const_mul c1
  refine h4.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hv] with t ht
  exact jacquet_eq_cc ha ht

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.KP.G2a_Dx
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup
/-! # WP-G2a, file 8: the mixed first `x`-derivative `∂_m` and Fourier series

`∂^{(+1)} = ∂_x`, `∂^{(−1)} = ∂_x̄` (Wirtinger, `K.dz`, `K.dzbar`) in one coordinate `x_w` of
`x : InfinitePlace F → ℂ`; `∂_m = ∏_w ∂^{(m_w)}_{x_w}` (MATH3 §0), defined by iterating over a
list of places.

* `Dw m w f`: the Wirtinger derivative of type `m` in the `w`-th coordinate.
* `DList m l f`: iteration over the list `l`; `Dm m f := DList m Finset.univ.toList f`.
* **`DList_series`**: for a Fourier series `Σ_i c_i e_∞(ν_i x)` whose coefficients are summable
  against every power of `1 + ‖ν_i‖`, `DList m l` acts termwise:
  the `i`-th term is multiplied by `∏_{w ∈ l} (−2πi · ν_{i,w}^{(m_w)})`.
-/

open scoped ComplexConjugate Topology
open NumberField

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.K ArtinKP.B

noncomputable section

/-! ### One complex variable -/

lemma linA_apply (a h : ℂ) : linA a h = 2 * Real.pi * Complex.I * (a * h + conj (a * h)) := by
  simp [linA]
  ring

lemma archChar_eq_exp_linA (a ζ : ℂ) : archChar (a * ζ) = Complex.exp (linA a ζ) := by
  rw [archChar, linA_apply]

lemma hasFDerivAt_archChar (a b ζ : ℂ) :
    HasFDerivAt (fun ζ : ℂ => archChar (a * (ζ - b))) (archChar (a * (ζ - b)) • linA a) ζ := by
  have h1 : HasFDerivAt (fun ζ : ℂ => linA a (ζ - b))
      ((linA a).comp (ContinuousLinearMap.id ℝ ℂ)) ζ :=
    (linA a).hasFDerivAt.comp ζ ((hasFDerivAt_id ζ).sub_const b)
  rw [ContinuousLinearMap.comp_id] at h1
  have h2 := h1.cexp
  simp only [← archChar_eq_exp_linA] at h2
  exact h2

/-! ### Several variables -/

/-! ### Constants are killed -/

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.KP.G2a_Block
/-! # WP-G2a, file 11: first derivatives in a block `(x_w, v_w)`

* `exists_major_prod`: the majorant of `G2a_Major` for an arbitrary product of one-place factors
  satisfying the one-place bound.
* `serA Φ q x v = Σ_ν q(ν)·τ_Φ(ν)·W_{4/3}(ν; v)·e_∞(νx)` in ambient coordinates.
* **`differentiableAt_block`**: for `q` of polynomial growth, `serA Φ q` is differentiable in the
  block `(x_w, v_w)` at every point with `v > 0`, the other coordinates fixed (termwise, with a
  summable majorant of the differentials on `ℂ × (a, b)`: MATH3 (Exp), "first partial derivatives
  in each block, locally uniformly").
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology Classical
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N ArtinKP.K

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}
variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

variable {hG hz6} {g : AllowedGen ι 𝔪}

/-! ### The differential of one term in a block -/

lemma hasFDerivAt_block_oai {a : ℂ} (ha : a ≠ 0) (b : ℂ) {z : ℂ × ℝ} (hz : 0 < z.2) :
    HasFDerivAt (fun z : ℂ × ℝ => archChar (a * (z.1 - b)) * jacquet (4 / 3) a z.2)
      (blockD a b z) z := by
  have h1 : HasFDerivAt (fun z : ℂ × ℝ => archChar (a * (z.1 - b)))
      ((archChar (a * (z.1 - b)) • linA a).comp (ContinuousLinearMap.fst ℝ ℂ ℝ)) z :=
    (hasFDerivAt_archChar a b z.1).comp z hasFDerivAt_fst
  have h2 : HasFDerivAt (fun z : ℂ × ℝ => jacquet (4 / 3) a z.2)
      (((1 : ℝ →L[ℝ] ℝ).smulRight (jd a z.2)).comp (ContinuousLinearMap.snd ℝ ℂ ℝ)) z :=
    (hasDerivAt_jacquet ha hz).hasFDerivAt.comp z hasFDerivAt_snd
  exact h1.mul h2

end

end ArtinKP.G2a
end

theorem solution : type_of% @ArtinKP.G2a.hasFDerivAt_block_oai := @ArtinKP.G2a.hasFDerivAt_block_oai
