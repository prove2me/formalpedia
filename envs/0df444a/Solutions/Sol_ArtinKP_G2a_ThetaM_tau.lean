-- Prove2me | solution 1 for ArtinKP.G2a.ThetaM_tau
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:07:50.571945+00:00
-- url     : https://prove2.me/submissions/7bf93896-becd-4de6-9814-db3c9781707e

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
import Theorems.Thm_ArtinKP_G2a_exists_major

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
open ArtinPrimitiveRoots.L3J (gA kappa0 )

noncomputable section

/-! ## The functions `g_a` -/

/-! ## The family `cc a b` -/

/-! ## Bounds for `cc a b` -/

/-! ## `κ₀` is a K-Bessel function -/

/-! ## The Bessel profile `κ(t) = t K_{1/3}(c√t)` -/

theorem kappaB_of_pos (c : ℝ) {t : ℝ} (ht : 0 < t) :
    kappaB c t = t * besselKR (1 / 3) (c * Real.sqrt t) := if_pos ht

/-! ## Smoothness and derivative bounds in the logarithmic variable -/

end

end ArtinKP.K
end

section
-- module Solutions.Artin.KP.T_Arch
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-T, file 2: the archimedean Whittaker function as a function on `X`

`WX s ν P = Winf s ν P.v = ∏_w jacquet s (−σ_w ν) v_w`.  For `Re s > 1`:

* `continuous_WX`, `differentiableOn_WX` (in `s`, `ν ≠ 0`), `exists_norm_WX_le` (bounded on
  `ball × box`);
* **`exists_WX_ne_zero`**: for every `s₁` (complex!) there is `δ > 0` with `WX s₁ ν P ≠ 0` whenever
  all `v_w < δ`.  (The Jacquet integral is `v^{2−s}·ĝ_s(νv)` with `ĝ_s` continuous and
  `ĝ_s(0) = π/(s−1) ≠ 0`; no information on zeros of `K_μ` of complex order is needed.)
* `phaseW s₁ ν`, a measurable test function of `v` of modulus `≤ 1` with
  `conj (phaseW s₁ ν P.v) * WX s₁ ν P = ‖WX s₁ ν P‖`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

/-! ### One place -/

/-! ### The function on `X` -/

variable {F : Type*} [Field F] [NumberField F]

lemma WX_mk (s : ℂ) (ν : F) (x : InfinitePlace F → ℂ) {v : InfinitePlace F → ℝ}
    (hv : ∀ w, 0 < v w) : WX s ν (X.mk x v hv) = Winf s ν v := rfl

/-! ### The phase test function -/

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.G2a_Def
/-! # WP-G2a, file 3: the series `thetaS` (definition, convergence, continuity, linearity)

`term Φ ν Q = τ_Φ(ν)·W_{4/3}(ν; v)·e_∞(νx)` (`Q = (x, v)`), `thetaS Φ Q = Σ_{ν ∈ R∖0} term Φ ν Q`.
Under Theorem E (`ThmE`) the series converges absolutely, uniformly on every set `vOpen n`
(`v ∈ (1/(n+1), n+1)^r`, any `x`), together with every polynomial weight `∏_w (1+|ν|_w)^p`;
`thetaS Φ` is continuous on `X F`, additive in `Φ` and homogeneous for `smulFun`.
-/

open scoped ComplexConjugate Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}
variable [IsTotallyComplex F]
variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

omit [IsTotallyComplex F] in
lemma vOpen_subset_vBox {n : ℕ} {Q : X F} (hQ : Q ∈ vOpen F n) : Q.v ∈ vBox F n :=
  fun w => ⟨(hQ w).1.le, (hQ w).2.le⟩

omit [IsTotallyComplex F] in
lemma exists_mem_vOpen (Q : X F) : ∃ n : ℕ, Q ∈ vOpen F n := by
  obtain ⟨n, hn⟩ := exists_nat_ge
    (∑ w : InfinitePlace F, (Q.v w + (Q.v w)⁻¹))
  refine ⟨n, fun w => ?_⟩
  have hpos := Q.v_pos w
  have hle : Q.v w + (Q.v w)⁻¹ ≤ n :=
    (Finset.single_le_sum (f := fun w => Q.v w + (Q.v w)⁻¹)
      (fun w _ => add_nonneg (Q.v_pos w).le (inv_nonneg.mpr (Q.v_pos w).le))
      (Finset.mem_univ w)).trans hn
  have hinv : 0 < (Q.v w)⁻¹ := inv_pos.mpr hpos
  constructor
  · rw [one_div, inv_lt_comm₀ (by positivity) hpos]
    linarith
  · linarith

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.KP.K_Weyl
/-! # WP-K, file 4: the Weyl flip on `H³ = SL₂(ℂ)/SU(2)`, and Fourier terms

Model: WP-X's `ArtinKP.X.H3 = {(x, v) : ℂ × ℝ | 0 < v}` with its `SL(2,ℂ)`-action; a right
`SU(2)`-invariant function on `SL₂(ℂ)` is `g ↦ f (g • j0)`, `j0 = (0, 1)`.

For `g = n(x) a(y)` (`a(y) = diag(y, y⁻¹)`, `y ∈ ℂˣ`), the two curves through `g • j0 = (x, |y|²)`
* `ζ ↦ g n(ζ) • j0 = (x + y² ζ, |y|²)`                               (`curveN`, `orbit_N`),
* `ζ ↦ g w n(ζ) • j0 = (x − y² ζ̄/(1+|ζ|²), |y|²/(1+|ζ|²))`           (`curveW`, `orbit_W`)
have Wirtinger derivatives at `ζ = 0` related by

  `∂_ζ (f ∘ curveW) = −∂_ζ̄ (f ∘ curveN)`,  `∂_ζ̄ (f ∘ curveW) = −∂_ζ (f ∘ curveN)`   (`weyl_flip`):

right translation by `w` exchanges the derivatives of weight `+1` and `−1` along `n(ζ)`, up to
the sign `−1` (MATH §4.5 "Weyl element"; `Ad(w) X_ζ = Y_{−ζ} ≡ X_{−ζ̄}` mod `𝔰𝔲(2)`).
On a Fourier term `f(x, v) = e(Tr νx) W(v)`: `∂_ζ (f ∘ curveN) = 2πi ν y² f`,
`∂_ζ̄ (f ∘ curveN) = 2πi conj(ν y²) f` (`dz_fourierTerm_curveN`), hence
`∂_ζ (f ∘ curveW) = −2πi conj(ν y²) f`, `∂_ζ̄ (f ∘ curveW) = −2πi ν y² f` (`weyl_flip_fourierTerm`).
-/

open scoped MatrixGroups ComplexConjugate

namespace ArtinKP.K

open ArtinKP.X

noncomputable section

/-! ## Matrices and orbits -/

/-! ## Wirtinger derivatives and the flip -/

/-! ## Fourier terms -/

/-! ## The Whittaker function at `s = 4/3` and the profile `κ` -/

/-- At `s = 4/3` the Jacquet integral is the Bessel profile: with `t = (|ν| v)²` (the normalized
absolute value of `ν y`, `|y|_w = v²`),
`|ν|² v · jacquet (4/3) ν v = (2π/Γ(4/3)) (2π|ν|)^{1/3} · κ(t)`, `κ = kappaB (4π)`. -/
theorem jacquet_four_thirds_kappaB {ν : ℂ} (hν : ν ≠ 0) {v : ℝ} (hv : 0 < v) :
    ((‖ν‖ ^ 2 * v : ℝ) : ℂ) * jacquet (4 / 3) ν v =
      (2 * Real.pi : ℂ) / Complex.Gamma (4 / 3) * ((2 * Real.pi * ‖ν‖ : ℝ) : ℂ) ^ ((4 / 3 : ℂ) - 1) *
        (kappaB (4 * Real.pi) ((‖ν‖ * v) ^ 2) : ℂ) := by
  have hn : 0 < ‖ν‖ := norm_pos_iff.2 hν
  have ht : 0 < (‖ν‖ * v) ^ 2 := by positivity
  rw [jacquet_eq (4 / 3) (by norm_num) hν hv, kappaB_of_pos _ ht, Real.sqrt_sq (by positivity),
    show (4 / 3 : ℂ) - 1 = ((1 / 3 : ℝ) : ℂ) by push_cast; norm_num, besselK_ofReal,
    show 4 * Real.pi * ‖ν‖ * v = 4 * Real.pi * (‖ν‖ * v) by ring]
  push_cast
  ring

end

end ArtinKP.K
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

lemma norm_linA_le (a : ℂ) : ‖linA a‖ ≤ 4 * Real.pi * ‖a‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rw [linA_apply, norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have : ‖a * h + conj (a * h)‖ ≤ 2 * (‖a‖ * ‖h‖) := by
    refine (norm_add_le _ _).trans ?_
    rw [RCLike.norm_conj, norm_mul]
    linarith
  nlinarith [Real.pi_pos]

lemma hasFDerivAt_archChar (a b ζ : ℂ) :
    HasFDerivAt (fun ζ : ℂ => archChar (a * (ζ - b))) (archChar (a * (ζ - b)) • linA a) ζ := by
  have h1 : HasFDerivAt (fun ζ : ℂ => linA a (ζ - b))
      ((linA a).comp (ContinuousLinearMap.id ℝ ℂ)) ζ :=
    (linA a).hasFDerivAt.comp ζ ((hasFDerivAt_id ζ).sub_const b)
  rw [ContinuousLinearMap.comp_id] at h1
  have h2 := h1.cexp
  simp only [← archChar_eq_exp_linA] at h2
  exact h2

lemma dz_eq (φ : ℂ → ℂ) (ζ : ℂ) : dz φ ζ = dzL (fderiv ℝ φ ζ) := by simp [dz, dzL]

lemma dzbar_eq (φ : ℂ → ℂ) (ζ : ℂ) : dzbar φ ζ = dzbarL (fderiv ℝ φ ζ) := by
  simp [dzbar, dzbarL]
  ring

lemma dzL_smul_linA (t a : ℂ) : dzL (t • linA a) = t * (2 * Real.pi * Complex.I * a) := by
  simp only [dzL, FunLike.coe_smul, FunLike.coe_sub, Pi.smul_apply, Pi.sub_apply,
    ContinuousLinearMap.apply_apply, linA_apply, smul_eq_mul, mul_one, map_mul, Complex.conj_I]
  linear_combination (-(t * Real.pi * Complex.I * (a - conj a))) * Complex.I_sq

lemma dzbarL_smul_linA (t a : ℂ) :
    dzbarL (t • linA a) = t * (2 * Real.pi * Complex.I * conj a) := by
  simp only [dzbarL, FunLike.coe_smul, FunLike.coe_add, Pi.smul_apply, Pi.add_apply,
    ContinuousLinearMap.apply_apply, linA_apply, smul_eq_mul, mul_one, map_mul, Complex.conj_I]
  linear_combination (t * Real.pi * Complex.I * (a - conj a)) * Complex.I_sq

lemma norm_cj (m : ℤ) (z : ℂ) : ‖cj m z‖ = ‖z‖ := by
  unfold cj; split_ifs <;> simp

/-! ### Several variables -/

variable {W : Type*} [Fintype W] [DecidableEq W]

lemma norm_eW (ν x : W → ℂ) : ‖eW ν x‖ = 1 := by
  simp only [eW, norm_prod, archChar_norm, Finset.prod_const_one]

lemma eW_update (ν x : W → ℂ) (w : W) (ζ : ℂ) :
    eW ν (Function.update x w ζ) = eW ν x * archChar (-(ν w) * (ζ - x w)) := by
  unfold eW
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w), ← Finset.mul_prod_erase _
    (fun w' => archChar (-(ν w' * x w'))) (Finset.mem_univ w), Function.update_self]
  have h : ∏ w' ∈ Finset.univ.erase w, archChar (-(ν w' * Function.update x w ζ w'))
      = ∏ w' ∈ Finset.univ.erase w, archChar (-(ν w' * x w')) :=
    Finset.prod_congr rfl fun w' hw' => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hw')]
  rw [h, show -(ν w * ζ) = -(ν w * x w) + -(ν w) * (ζ - x w) by ring, archChar_add]
  ring

variable {I : Type*}

/-- **One step**: the derivative of a Fourier series in one coordinate, termwise. -/
theorem Dw_series (c : I → ℂ) (ν : I → W → ℂ)
    (hs : Summable fun i => ‖c i‖ * (1 + ‖ν i‖)) (m : ℤ) (w : W) (x : W → ℂ) :
    Dw m w (fun x => ∑' i, c i * eW (ν i) x) x =
      ∑' i, c i * (-(2 * Real.pi * Complex.I) * cj m (ν i w)) * eW (ν i) x := by
  set f : I → ℂ → ℂ := fun i ζ => c i * eW (ν i) (Function.update x w ζ) with hf
  set f' : I → ℂ → (ℂ →L[ℝ] ℂ) := fun i ζ =>
    (c i * (eW (ν i) x * archChar (-(ν i w) * (ζ - x w)))) • linA (-(ν i w)) with hf'
  have hd : ∀ i ζ, HasFDerivAt (f i) (f' i ζ) ζ := by
    intro i ζ
    have e : f i = fun ζ => (c i * eW (ν i) x) * archChar (-(ν i w) * (ζ - x w)) := by
      funext ζ; simp only [hf, eW_update]; ring
    rw [e]
    have := (hasFDerivAt_archChar (-(ν i w)) (x w) ζ).const_mul (c i * eW (ν i) x)
    simpa only [hf', smul_smul, mul_assoc] using this
  set u : I → ℝ := fun i => 4 * Real.pi * (‖c i‖ * (1 + ‖ν i‖)) with hu
  have hus : Summable u := hs.mul_left _
  have hb : ∀ i ζ, ‖f' i ζ‖ ≤ u i := by
    intro i ζ
    rw [norm_smul, norm_mul, norm_mul, norm_eW, archChar_norm, mul_one, mul_one]
    have h1 := norm_linA_le (-(ν i w))
    rw [norm_neg] at h1
    have h2 : ‖ν i w‖ ≤ 1 + ‖ν i‖ := (norm_le_pi_norm (ν i) w).trans (by linarith)
    calc ‖c i‖ * ‖linA (-(ν i w))‖ ≤ ‖c i‖ * (4 * Real.pi * (1 + ‖ν i‖)) :=
          mul_le_mul_of_nonneg_left
            (h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))) (norm_nonneg _)
      _ = u i := by rw [hu]; ring
  have h0 : Summable fun i => f i (x w) := by
    refine Summable.of_norm_bounded hs fun i => ?_
    rw [hf, norm_mul, norm_eW, mul_one]
    exact le_mul_of_one_le_right (norm_nonneg _) (by linarith [norm_nonneg (ν i)])
  have H := hasFDerivAt_tsum hus hd hb h0 (x w)
  have hsL : Summable fun i => f' i (x w) := Summable.of_norm_bounded hus fun i => hb i (x w)
  have hval : ∀ i, f' i (x w) = (c i * eW (ν i) x) • linA (-(ν i w)) := fun i => by
    simp only [hf', sub_self, mul_zero]
    rw [show archChar 0 = 1 by simp [archChar], mul_one]
  have hfun : (fun ζ => (fun x => ∑' i, c i * eW (ν i) x) (Function.update x w ζ))
      = fun ζ => ∑' i, f i ζ := rfl
  unfold Dw
  split_ifs with hm
  · rw [hfun, dz_eq, H.fderiv, ← (hsL.hasSum.mapL dzL).tsum_eq]
    refine tsum_congr fun i => ?_
    rw [hval, dzL_smul_linA, cj, if_pos hm]
    ring
  · rw [hfun, dzbar_eq, H.fderiv, ← (hsL.hasSum.mapL dzbarL).tsum_eq]
    refine tsum_congr fun i => ?_
    rw [hval, dzbarL_smul_linA, cj, if_neg hm, map_neg]
    ring

lemma eig_nil (m : W → ℤ) (ν : W → ℂ) : eig m [] ν = 1 := rfl

lemma eig_cons (m : W → ℤ) (w : W) (l : List W) (ν : W → ℂ) :
    eig m (w :: l) ν = -(2 * Real.pi * Complex.I) * cj (m w) (ν w) * eig m l ν := by
  simp [eig]

lemma norm_eig_le (m : W → ℤ) (l : List W) (ν : W → ℂ) :
    ‖eig m l ν‖ ≤ (2 * Real.pi * (1 + ‖ν‖)) ^ l.length := by
  induction l with
  | nil => simp [eig]
  | cons w l ih =>
    rw [eig_cons, norm_mul, List.length_cons, pow_succ']
    refine mul_le_mul ?_ ih (norm_nonneg _) (by positivity)
    rw [norm_mul, norm_neg, norm_cj, norm_mul, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm ν w).trans (by linarith)) (by positivity)

lemma eig_univ (m : W → ℤ) (ν : W → ℂ) :
    eig m Finset.univ.toList ν = ∏ w, (-(2 * Real.pi * Complex.I) * cj (m w) (ν w)) := by
  rw [eig, Finset.prod_map_toList]

/-- **Termwise action of the iterated Wirtinger derivatives on a Fourier series.** -/
theorem DList_series (m : W → ℤ) (l : List W) (c : I → ℂ) (ν : I → W → ℂ)
    (hs : ∀ p : ℕ, Summable fun i => ‖c i‖ * (1 + ‖ν i‖) ^ p) :
    DList m l (fun x => ∑' i, c i * eW (ν i) x) =
      fun x => ∑' i, c i * eig m l (ν i) * eW (ν i) x := by
  induction l with
  | nil => funext x; simp [DList, eig_nil]
  | cons w l ih =>
    funext x
    have hs' : Summable fun i => ‖c i * eig m l (ν i)‖ * (1 + ‖ν i‖) := by
      refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
        ((hs (l.length + 1)).mul_left ((2 * Real.pi) ^ l.length))
      rw [norm_mul]
      have h1 := norm_eig_le m l (ν i)
      have h0 : (0 : ℝ) ≤ 1 + ‖ν i‖ := by positivity
      calc ‖c i‖ * ‖eig m l (ν i)‖ * (1 + ‖ν i‖)
          ≤ ‖c i‖ * (2 * Real.pi * (1 + ‖ν i‖)) ^ l.length * (1 + ‖ν i‖) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) h0
        _ = (2 * Real.pi) ^ l.length * (‖c i‖ * (1 + ‖ν i‖) ^ (l.length + 1)) := by
            rw [mul_pow, pow_succ]; ring
    show Dw (m w) w (DList m l fun x => ∑' i, c i * eW (ν i) x) x = _
    rw [ih, Dw_series (fun i => c i * eig m l (ν i)) ν hs' (m w) w x]
    refine tsum_congr fun i => ?_
    rw [eig_cons]
    ring

/-! ### Constants are killed -/

omit [Fintype W] in
lemma Dw_const_add (m : ℤ) (w : W) (C : ℂ) (g : (W → ℂ) → ℂ) :
    Dw m w (fun x => C + g x) = Dw m w g := by
  funext x
  simp only [Dw, dz, dzbar, fderiv_const_add]

omit [Fintype W] in
/-- A constant added to the function does not change `DList m l`, `l ≠ []`. -/
lemma DList_const_add (m : W → ℤ) (l : List W) (hl : l ≠ []) (C : ℂ) (g : (W → ℂ) → ℂ) :
    DList m l (fun x => C + g x) = DList m l g := by
  induction l with
  | nil => exact absurd rfl hl
  | cons w l ih =>
    by_cases h : l = []
    · subst h
      exact Dw_const_add (m w) w C g
    · show Dw (m w) w (DList m l fun x => C + g x) = Dw (m w) w (DList m l g)
      rw [ih h]

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.KP.G2a_Fwd
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex
/-! # WP-G2a, file 9: `∂_m θ̃_Φ` termwise and the forward field (MATH3 §1.1)

* `thetaX Φ v hv x = θ̃_Φ(x, v)` as a function of `x` at fixed height `v`.
* **`Dm_thetaX`**: `∂_m θ̃_Φ(·, v)` is the termwise series; the constant term is killed and the
  `ν`-th term is multiplied by `∏_w (−2πi·ν_w^{(m_w)})`.
* `ThetaM m Φ X Y := ∏_w Y_w^{(m_w)} · (∂_m θ̃_Φ)(X, |Y|)` (MATH3's `Θ_m^Φ(X, Y)`).
* `place_kappaB`: `(νY)^{(m)}·jacquet (4/3) (−ν) |Y| = C0·|ν|^{−2/3}·ω_m(νY)·κ(|νY|²)`,
  `κ = K.kappaB (4π)`, `C0 = (2π)^{4/3}/Γ(4/3)`.
* **`ThetaM_tau`**: the expansion with coefficient `τ_Φ(ν)` (no Theorem E beyond convergence);
* **`ThetaM_forward`** = MATH3 (1.1):
  `Θ_m^Φ(X,Y) = kapC·C_a^r·Σ_ν coef^S(ν)·ξ_Φ(ν)·e_∞(νX)·∏_w ω_{m_w}(ν_wY_w)·κ(|ν_wY_w|²)`,
  `C_a = −2πi·C0`, with `summable_forward`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology Classical
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N ArtinKP.K

noncomputable section

/-! ### One place -/

lemma cj_mul (m : ℤ) (a b : ℂ) : cj m (a * b) = cj m a * cj m b := by
  unfold cj; split_ifs <;> simp

theorem place_kappaB (m : ℤ) {a Y : ℂ} (ha : a ≠ 0) (hY : Y ≠ 0) :
    cj m (a * Y) * jacquet (4 / 3) (-a) ‖Y‖ =
      C0 * ((‖a‖ ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * omg m (a * Y) *
        (kappaB (4 * Real.pi) (‖a * Y‖ ^ 2) : ℂ) := by
  have hr : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hy : 0 < ‖Y‖ := norm_pos_iff.mpr hY
  have h := jacquet_four_thirds_kappaB (ν := -a) (neg_ne_zero.mpr ha) hy
  rw [norm_neg, show (4 / 3 : ℂ) - 1 = ((1 / 3 : ℝ) : ℂ) by push_cast; norm_num,
    ← Complex.ofReal_cpow (by positivity), Real.mul_rpow (by positivity) hr.le] at h
  have key : ‖a‖ ^ (1 / 3 : ℝ) = ‖a‖ ^ (-(2 / 3 : ℝ)) * ‖a‖ := by
    conv_rhs => rw [← Real.rpow_one ‖a‖, ← Real.rpow_mul hr.le, ← Real.rpow_add hr]
    norm_num
  rw [key] at h
  have hne : ((‖a‖ ^ 2 * ‖Y‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hrC : (‖a‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hyC : (‖Y‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  refine mul_left_cancel₀ hne ?_
  rw [mul_left_comm, h, omg, norm_mul, C0]
  push_cast
  field_simp

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}
variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

lemma eW_emb (ν : F) (x : InfinitePlace F → ℂ) : eW (emb ν) x = eInf (emb ν * x) := rfl

lemma thetaX_eq (Φ : GSection ι P 𝔪) (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) :
    thetaX hG hz6 Φ v hv = fun x => zc hG hz6 Φ * htC (2 / 3) (X.mk 0 v hv) +
      ∑' ν : {ν : SInt 𝔪 // ν ≠ 0},
        (kapC F * (T.tau hG hz6 Φ (ν : SInt 𝔪) * Winf (4 / 3) ((ν : SInt 𝔪) : F) v)) *
          eW (emb ((ν : SInt 𝔪) : F)) x := by
  funext x
  unfold thetaX thetaT thetaS
  rw [← tsum_mul_left]
  congr 1
  refine tsum_congr fun ν => ?_
  rw [eW_emb]
  simp only [term, X.x_mk, T.WX_mk]
  ring

omit [IsTotallyComplex F] in
lemma one_add_norm_emb_le (ν : F) :
    1 + ‖(emb ν : InfinitePlace F → ℂ)‖ ≤ ∏ w : InfinitePlace F, (1 + w ν) := by
  have h1 : (1 : ℝ) ≤ ∏ w : InfinitePlace F, (1 + w ν) := by
    calc (1 : ℝ) = ∏ _w : InfinitePlace F, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one)
        fun w _ => by linarith [apply_nonneg w ν]
  have h2 : ‖(emb ν : InfinitePlace F → ℂ)‖ ≤ ∏ w : InfinitePlace F, (1 + w ν) - 1 := by
    rw [pi_norm_le_iff_of_nonneg (by linarith)]
    intro w
    rw [emb_apply, InfinitePlace.norm_embedding_eq]
    have : (1 + w ν) = ∏ w' : InfinitePlace F, (if w' = w then 1 + w ν else 1) := by
      rw [Finset.prod_ite_eq' Finset.univ w, if_pos (Finset.mem_univ w)]
    have h3 : 1 + w ν ≤ ∏ w' : InfinitePlace F, (1 + w' ν) := by
      rw [this]
      refine Finset.prod_le_prod (fun w' _ => by split_ifs <;> positivity) fun w' _ => ?_
      split_ifs with h
      · rw [h]
      · linarith [apply_nonneg w' ν]
    linarith
  linarith

variable {hG hz6} {g : AllowedGen ι 𝔪}

/-- The coefficients of `θ̃_Φ(·, v)` are summable against every power of `1 + ‖ν‖`. -/
theorem summable_coef_pow (hE : ThmE hG hz6 g P) (Φ : GSection ι P 𝔪)
    (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) (p : ℕ) :
    Summable fun ν : {ν : SInt 𝔪 // ν ≠ 0} =>
      ‖kapC F * (T.tau hG hz6 Φ (ν : SInt 𝔪) * Winf (4 / 3) ((ν : SInt 𝔪) : F) v)‖ *
        (1 + ‖(emb ((ν : SInt 𝔪) : F) : InfinitePlace F → ℂ)‖) ^ p := by
  obtain ⟨n₀, hn₀⟩ := exists_mem_vOpen (X.mk 0 v hv)
  have hvb : v ∈ vBox F n₀ := vOpen_subset_vBox hn₀
  obtain ⟨u, hu, -, hle⟩ := exists_major hE Φ p n₀
  refine Summable.of_nonneg_of_le (fun ν => by positivity) (fun ν => ?_) (hu.mul_left ‖kapC F‖)
  rw [norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine le_trans ?_ (hle ν v hvb)
  rw [mul_comm, Finset.prod_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) (one_add_norm_emb_le _) p) (norm_nonneg _)

/-- **`∂_m θ̃_Φ(·, v)`, termwise.** -/
theorem Dm_thetaX (hE : ThmE hG hz6 g P) (m : InfinitePlace F → ℤ) (Φ : GSection ι P 𝔪)
    (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) (x : InfinitePlace F → ℂ) :
    Dm m (thetaX hG hz6 Φ v hv) x = kapC F * ∑' ν : {ν : SInt 𝔪 // ν ≠ 0},
      T.tau hG hz6 Φ (ν : SInt 𝔪) * Winf (4 / 3) ((ν : SInt 𝔪) : F) v *
        (∏ w : InfinitePlace F, (-(2 * Real.pi * Complex.I) *
          cj (m w) (w.embedding ((ν : SInt 𝔪) : F)))) * eInf (emb ((ν : SInt 𝔪) : F) * x) := by
  have hne : (Finset.univ : Finset (InfinitePlace F)).toList ≠ [] := by
    rw [ne_eq, Finset.toList_eq_nil]
    exact Finset.univ_nonempty.ne_empty
  rw [thetaX_eq, Dm, DList_const_add m _ hne,
    DList_series m _ _ _ (summable_coef_pow hE Φ v hv), ← tsum_mul_left]
  refine tsum_congr fun ν => ?_
  rw [eig_univ, eW_emb]
  simp only [emb_apply]
  ring

variable (hG hz6)

variable {hG hz6}

/-- The `ν`-th term of `Θ_m^Φ(X,Y)` in Bessel form. -/
lemma term_kappaB (m : InfinitePlace F → ℤ) {ν : F} (hν : ν ≠ 0) (Y : InfinitePlace F → ℂ)
    (hY : ∀ w, Y w ≠ 0) :
    (∏ w, cj (m w) (Y w)) * (Winf (4 / 3) ν (fun w => ‖Y w‖) *
      ∏ w : InfinitePlace F, (-(2 * Real.pi * Complex.I) * cj (m w) (w.embedding ν))) =
      (-(2 * Real.pi * Complex.I) * C0) ^ Fintype.card (InfinitePlace F) *
        ((∏ w : InfinitePlace F, (w ν) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) *
        ∏ w : InfinitePlace F, (omg (m w) (w.embedding ν * Y w) *
          (kappaB (4 * Real.pi) (‖w.embedding ν * Y w‖ ^ 2) : ℂ)) := by
  unfold Winf
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.card_univ,
    ← Finset.prod_const, Complex.ofReal_prod, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h := place_kappaB (m w) ((map_ne_zero w.embedding).mpr hν) (hY w)
  rw [InfinitePlace.norm_embedding_eq, cj_mul] at h
  linear_combination (-(2 * Real.pi * Complex.I)) * h

/-- **The expansion of `Θ_m^Φ` with coefficient `τ_Φ(ν)`.** -/
theorem ThetaM_tau_oai (hE : ThmE hG hz6 g P) (m : InfinitePlace F → ℤ) (Φ : GSection ι P 𝔪)
    (X Y : InfinitePlace F → ℂ) (hY : ∀ w, Y w ≠ 0) :
    ThetaM hG hz6 m Φ X Y hY =
      kapC F * (-(2 * Real.pi * Complex.I) * C0) ^ Fintype.card (InfinitePlace F) *
        ∑' ν : {ν : SInt 𝔪 // ν ≠ 0}, T.tau hG hz6 Φ (ν : SInt 𝔪) *
          ((∏ w : InfinitePlace F, (w ((ν : SInt 𝔪) : F)) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) *
          eInf (emb ((ν : SInt 𝔪) : F) * X) *
          ∏ w : InfinitePlace F, (omg (m w) (w.embedding ((ν : SInt 𝔪) : F) * Y w) *
            (kappaB (4 * Real.pi) (‖w.embedding ((ν : SInt 𝔪) : F) * Y w‖ ^ 2) : ℂ)) := by
  rw [ThetaM, Dm_thetaX hE, mul_left_comm, mul_assoc (kapC F)]
  congr 1
  rw [← tsum_mul_left (a := ∏ w, cj (m w) (Y w)),
    ← tsum_mul_left (a := (-(2 * Real.pi * Complex.I) * C0) ^ Fintype.card (InfinitePlace F))]
  refine tsum_congr fun ν => ?_
  have h := term_kappaB m (H0.coe_ne_zero ν) Y hY
  linear_combination (T.tau hG hz6 Φ (ν : SInt 𝔪) * eInf (emb ((ν : SInt 𝔪) : F) * X)) * h

end

end ArtinKP.G2a
end

theorem solution.{u_1} : type_of% @ArtinKP.G2a.ThetaM_tau_oai.{u_1} := @ArtinKP.G2a.ThetaM_tau_oai.{u_1}
