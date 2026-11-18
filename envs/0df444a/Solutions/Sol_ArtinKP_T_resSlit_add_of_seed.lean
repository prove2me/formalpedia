-- Prove2me | solution 1 for ArtinKP.T.resSlit_add_of_seed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:46:36.498302+00:00
-- url     : https://prove2.me/submissions/83662ee3-d849-4f0e-8801-8a742d247074

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
import Definitions.Def_ArtinKPB015
import Theorems.Thm_ArtinKP_B_continuous_eis
import Theorems.Thm_ArtinKP_GL_eisEigen_of_two_lt_re
import Theorems.Thm_ArtinKP_N_coeff_resPart_add_hInt
import Theorems.Thm_ArtinKP_T_differentiableOn_Afun
import Theorems.Thm_ArtinKP_T_tendsto_ray_Afun
import Theorems.Thm_ArtinKP_X_X_isPOU_pou
import Theorems.Thm_ArtinKP_X_X_tsum_indicator_box_le_boxMult

section
-- module Solutions.Artin.KP.B1_L2
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
attribute [-simp] _root_.ArtinKP.X.chart1_symm_fst _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart1_x _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
/-! # WP-B1, file 9: `G ∈ L¹ ∩ L²(Γ\X)`, and compactness of the truncated space at the cusp `∞`

* `measurable_G`; `lintegral_G_pow_lt_top`: `∫_{Γ\X} G^k dμ < ∞` (in the partition-of-unity form of
  WP-X) for every `k`, from the boundedness of `G` and **finite volume of `Γ\X`** (hypothesis `hvol`).
* `H3.isCompact_box`, `X.isCompact_box`.
* `exists_reduced`: every point of `X` is `Γ_∞`-equivalent (`Γ_∞ ⊂ SL₂(𝓞_F)` upper triangular) to a point
  with `x` in the fundamental cell and balanced `v`; `siegel S' T` is compact; hence
  `subset_orbit_siegel`: the points whose top class is in the `SL₂(𝓞_F)`-orbit of `∞` and whose top
  height is in `[c, T]` lie in `SL₂(𝓞_F) · (compact)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {S : Finset (FinitePlace F)}

/-! ### Compactness of the truncated space at the cusp `∞` (item 5) -/

omit [NumberField F] [IsTotallyComplex F] in
lemma H3.isCompact_box {m M B : ℝ} (hm : 0 < m) : IsCompact (H3.box m M B) := by
  have hind : Topology.IsInducing (Subtype.val : {p : ℂ × ℝ // 0 < p.2} → ℂ × ℝ) :=
    Topology.IsInducing.subtypeVal
  have himg : (Subtype.val : {p : ℂ × ℝ // 0 < p.2} → ℂ × ℝ) '' (H3.box m M B) =
      Metric.closedBall (0 : ℂ) B ×ˢ Set.Icc m M := by
    ext ⟨z, t⟩
    constructor
    · rintro ⟨Q, ⟨h1, h2, h3⟩, hQ⟩
      have hz : H3.x Q = z := congrArg Prod.fst hQ
      have ht : H3.v Q = t := congrArg Prod.snd hQ
      rw [hz] at h1
      rw [ht] at h2 h3
      exact ⟨by simpa using h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      have h1' : ‖z‖ ≤ B := by simpa using h1
      exact ⟨⟨(z, t), lt_of_lt_of_le hm h2⟩, ⟨h1', h2, h3⟩, rfl⟩
  exact hind.isCompact_iff.mpr (himg ▸ (isCompact_closedBall 0 B).prod isCompact_Icc)

omit [IsTotallyComplex F] in
theorem isCompact_siegelBox {m M B : ℝ} (hm : 0 < m) : IsCompact (siegelBox F m M B) := by
  have : siegelBox F m M B = Set.pi Set.univ fun _ : InfinitePlace F => H3.box m M B := by
    ext P; simp [siegelBox]
  rw [this]
  exact isCompact_univ_pi fun _ => H3.isCompact_box hm

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.K_Bessel
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

theorem besselKer_pos (z t : ℝ) : 0 < besselKer z t := Real.exp_pos _

theorem besselKer_inv (z t : ℝ) : besselKer z t⁻¹ = besselKer z t := by
  unfold besselKer; rw [inv_inv, add_comm]

theorem besselKer_le_exp {z t : ℝ} (hz : 0 ≤ z) (ht : 0 < t) :
    besselKer z t ≤ Real.exp (-(z / 2) * t) := by
  unfold besselKer
  refine Real.exp_le_exp.2 ?_
  have : 0 ≤ z / 2 * t⁻¹ := by positivity
  nlinarith

theorem continuousOn_besselKer (z : ℝ) : ContinuousOn (besselKer z) (Ioi 0) := by
  unfold besselKer
  refine Real.continuous_exp.comp_continuousOn (continuousOn_const.mul
    (continuousOn_id.add (continuousOn_inv₀.mono fun t ht => ?_)))
  exact (ne_of_gt ht : t ≠ 0)

theorem locallyIntegrableOn_besselKer (z : ℝ) :
    LocallyIntegrableOn (fun t => (besselKer z t : ℂ)) (Ioi 0) :=
  (Complex.continuous_ofReal.comp_continuousOn (continuousOn_besselKer z)).locallyIntegrableOn
    measurableSet_Ioi

theorem besselKer_isBigO_atTop {z : ℝ} (hz : 0 < z) (a : ℝ) :
    (fun t => (besselKer z t : ℂ)) =O[atTop] (· ^ (-a)) := by
  have h1 : (fun t => (besselKer z t : ℂ)) =O[atTop] fun t : ℝ => Real.exp (-(z / 2) * t) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [Complex.norm_real, Real.norm_of_nonneg (besselKer_pos z t).le, one_mul,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    exact besselKer_le_exp hz.le ht
  exact h1.trans (isLittleO_exp_neg_mul_rpow_atTop (half_pos hz) _).isBigO

theorem besselKer_isBigO_zero {z : ℝ} (hz : 0 < z) (b : ℝ) :
    (fun t => (besselKer z t : ℂ)) =O[𝓝[>] 0] (· ^ (-b)) := by
  have h := (besselKer_isBigO_atTop hz (-b)).comp_tendsto tendsto_inv_nhdsGT_zero
  refine (h.congr' (Eventually.of_forall fun t => ?_) ?_)
  · simp only [Function.comp_apply, besselKer_inv]
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Function.comp_apply]
    rw [neg_neg, Real.inv_rpow (le_of_lt ht), Real.rpow_neg (le_of_lt ht)]

/-- `μ ↦ K_μ(z)` is entire, for `z > 0`. -/
theorem besselK_differentiable {z : ℝ} (hz : 0 < z) : Differentiable ℂ fun μ => besselK μ z := by
  intro μ
  unfold besselK
  exact (mellin_differentiableAt_of_isBigO_rpow (locallyIntegrableOn_besselKer z)
    (besselKer_isBigO_atTop hz (μ.re + 1)) (lt_add_one _)
    (besselKer_isBigO_zero hz (μ.re - 1)) (sub_one_lt _)).const_mul _

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
attribute [-instance] _root_.ArtinKP.X.instSigmaFiniteXVol
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

theorem archChar_zero : archChar 0 = 1 := by simp [archChar]

theorem continuous_archChar : Continuous archChar := by
  unfold archChar; fun_prop

/-! ## Radial integrals on `ℂ` (copied from OpenAI) -/

lemma integral_radial_sq (f : ℝ → ℂ) :
    (∫ z : ℂ, f (‖z‖ ^ 2)) = (Real.pi : ℂ) * ∫ t : ℝ in Set.Ioi 0, f t := by
  have hball : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
    simp [Measure.real, Complex.volume_ball]
  have hpolar := integral_fun_norm_addHaar (volume : Measure ℂ) (fun r : ℝ => f (r^2))
  have hsub := integral_comp_rpow_Ioi (E := ℂ) f (p := 2) (by norm_num)
  norm_num [Real.rpow_two, Real.rpow_one] at hsub
  simp only [Complex.finrank_real_complex, hball, Nat.reduceSub, pow_one,
    nsmul_eq_mul, Complex.real_smul, ] at hpolar hsub
  rw [hpolar]
  rw [← hsub]
  rw [show (fun x : ℝ => (2:ℂ)*x*f (x^2)) =
      (fun x : ℝ => (2:ℂ)*(x*f (x^2))) by funext x; ring, integral_const_mul]
  ring

lemma integrable_radial_sq_iff (f : ℝ → ℂ) :
    Integrable (fun z : ℂ => f (‖z‖ ^ 2)) ↔ IntegrableOn f (Set.Ioi 0) := by
  rw [integrable_fun_norm_addHaar (volume : Measure ℂ) (f := fun r : ℝ => f (r^2))]
  have h := integrableOn_Ioi_comp_rpow_iff' (E := ℂ) f (p := 2) (by norm_num)
  simpa only [Complex.finrank_real_complex, Nat.reduceSub, pow_one,
    show (2:ℝ)-1=1 by norm_num, Real.rpow_one, Real.rpow_two] using h

lemma add_one_image_Ioi : (fun x : ℝ => x+1) '' Set.Ioi 0 = Set.Ioi 1 := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    simp only [Set.mem_Ioi] at *
    linarith
  · intro hy
    refine ⟨y-1, ?_, by ring⟩
    simp only [Set.mem_Ioi] at *
    linarith

lemma integrable_add_one_Ioi_iff (f : ℝ → ℂ) :
    IntegrableOn (fun x : ℝ => f (x+1)) (Set.Ioi 0) ↔ IntegrableOn f (Set.Ioi 1) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi
    (fun x (hx : x ∈ Set.Ioi (0:ℝ)) => (hasDerivAt_id x |>.add_const 1).hasDerivWithinAt)
    (fun x hx y hy hxy => by dsimp at hxy; linarith : InjOn (fun x : ℝ => x+1) (Set.Ioi 0)) f
  simp only [id_eq] at h
  rw [add_one_image_Ioi] at h
  simpa only [abs_one, one_smul] using h.symm

lemma integral_add_one_Ioi (f : ℝ → ℂ) :
    (∫ x : ℝ in Set.Ioi 0, f (x+1)) = ∫ x : ℝ in Set.Ioi 1, f x := by
  have h := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi
    (fun x (hx : x ∈ Set.Ioi (0:ℝ)) => (hasDerivAt_id x |>.add_const 1).hasDerivWithinAt)
    (fun x hx y hy hxy => by dsimp at hxy; linarith : InjOn (fun x : ℝ => x+1) (Set.Ioi 0)) f
  simp only [id_eq] at h
  rw [add_one_image_Ioi] at h
  simpa only [abs_one, one_smul] using h.symm

lemma hyperbolicKernel_integrable (s : ℂ) (hs : 1 < s.re) :
    Integrable (hyperbolicKernel s) := by
  unfold hyperbolicKernel
  rw [integrable_radial_sq_iff (fun t : ℝ => ((1+t : ℝ) : ℂ)^(-s))]
  have h := (integrable_add_one_Ioi_iff (fun x : ℝ => (x : ℂ)^(-s))).mpr
    (integrableOn_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs) (by norm_num : (0:ℝ)<1))
  simpa only [add_comm] using h

theorem integral_hyperbolicKernel (s : ℂ) (hs : 1 < s.re) :
    (∫ z : ℂ, hyperbolicKernel s z) = (Real.pi : ℂ) / (s-1) := by
  unfold hyperbolicKernel
  rw [integral_radial_sq (fun t : ℝ => ((1+t : ℝ) : ℂ)^(-s))]
  simp_rw [add_comm (1:ℝ)]
  rw [integral_add_one_Ioi (fun t : ℝ => (t : ℂ)^(-s))]
  rw [integral_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs) (by norm_num : (0:ℝ)<1)]
  simp only [Complex.ofReal_one, Complex.one_cpow]
  have hn : (-s+1)⁻¹ = -(s-1)⁻¹ := by
    rw [show -s+1=-(s-1) by ring, inv_neg]
  simp only [div_eq_mul_inv, hn]
  ring

lemma continuous_hyperbolicKernel (s : ℂ) : Continuous (hyperbolicKernel s) := by
  unfold hyperbolicKernel
  apply Continuous.cpow
  · fun_prop
  · exact continuous_const
  · intro z
    exact Complex.ofReal_mem_slitPlane.mpr (by positivity)

lemma sourceFourierKernel_zero (s : ℂ) (hs : 1 < s.re) :
    sourceFourierKernel s 0 = (Real.pi : ℂ)/(s-1) := by
  simpa only [sourceFourierKernel, neg_zero, zero_mul, archChar_zero, mul_one]
    using integral_hyperbolicKernel s hs

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

/-- The right-hand side of `jacquet_eq` is entire in `s`. -/
theorem differentiable_jacquet_rhs (ν : ℂ) {v : ℝ} (hν : ν ≠ 0) (hv : 0 < v) :
    Differentiable ℂ fun s : ℂ =>
      (2 * Real.pi : ℂ) / Complex.Gamma s * ((2 * Real.pi * ‖ν‖ : ℝ) : ℂ) ^ (s - 1) *
        (v : ℂ) * besselK (s - 1) (4 * Real.pi * ‖ν‖ * v) := by
  have hz : 0 < 4 * Real.pi * ‖ν‖ * v := by
    have := norm_pos_iff.2 hν
    positivity
  have hc : ((2 * Real.pi * ‖ν‖ : ℝ) : ℂ) ≠ 0 := by
    have := norm_pos_iff.2 hν
    exact Complex.ofReal_ne_zero.2 (by positivity)
  have hG : Differentiable ℂ fun s : ℂ => (2 * Real.pi : ℂ) / Complex.Gamma s := by
    simpa [div_eq_mul_inv, one_div] using
      Complex.differentiable_one_div_Gamma.const_mul (2 * Real.pi : ℂ)
  have hP : Differentiable ℂ fun s : ℂ => ((2 * Real.pi * ‖ν‖ : ℝ) : ℂ) ^ (s - 1) := fun s =>
    (differentiableAt_id.sub_const 1).const_cpow (Or.inl hc)
  have hK : Differentiable ℂ fun s : ℂ => besselK (s - 1) (4 * Real.pi * ‖ν‖ * v) :=
    (besselK_differentiable hz).comp (differentiable_id.sub_const 1)
  exact ((hG.mul hP).mul_const _).mul hK

/-- `s ↦ jacquet s ν v` is holomorphic on `Re s > 1` (`ν ≠ 0`). -/
theorem differentiableOn_jacquet (ν : ℂ) {v : ℝ} (hν : ν ≠ 0) (hv : 0 < v) :
    DifferentiableOn ℂ (fun s => jacquet s ν v) {s : ℂ | 1 < s.re} :=
  (differentiable_jacquet_rhs ν hν hv).differentiableOn.congr fun s hs => jacquet_eq s hs hν hv

end

end ArtinKP.K
end

section
-- module Solutions.Artin.KP.B_FourArch
/-!
# WP-B, part 2: the characters and the archimedean integral

* `eInf x = ∏_w archChar (-x_w)` on `ℂ^r`; `eInf (emb a) = exp(-2πi Tr a)` for `a ∈ F`.
* `psiS h𝔪 : SfChar 𝔪`, `ψ_{S_f}(x) = sAddChar 𝔪 x · conj (eInf (emb x))`; it is trivial on
  `𝔩_0`, and `eInf (emb x) = sAddChar 𝔪 x · conj ψ_{S_f}(x)` (`eInf_emb_eq`).
* `kerA v x = ∏_w v_w / (|x_w|² + v_w²)`; `I_{(c,d)}(x, v) = N_∞(c)⁻¹ · kerA v (x + d/c)`.
* `Winf s ν v = ∏_w jacquet s (-σ_w ν) v_w`; the integral of a shifted kernel against
  `conj eInf(ν x)` (`integral_shift_kernel`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.K

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### The archimedean character -/

theorem archChar_neg (z : ℂ) : archChar (-z) = conj (archChar z) := by
  rw [archChar_eq_re, archChar_eq_re, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.neg_re, map_ofNat]
  push_cast
  ring

theorem continuous_archChar : Continuous archChar := by
  unfold archChar
  fun_prop

theorem continuous_eInf : Continuous (eInf : (InfinitePlace F → ℂ) → ℂ) :=
  continuous_finsetProd _ fun w _ =>
    continuous_archChar.comp (continuous_apply w).neg

/-! ### The `S_f`-character -/

/-! ### The archimedean kernel -/

theorem continuous_chiInf (ν : F) : Continuous (chiInf ν) :=
  Complex.continuous_conj.comp (continuous_eInf.comp (continuous_const.mul continuous_id))

theorem chiInf_eq_prod (ν : F) (x : InfinitePlace F → ℂ) :
    chiInf ν x = ∏ w, archChar (-(-(w.embedding ν)) * x w) := by
  rw [chiInf, eInf, map_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← archChar_neg, Pi.mul_apply, emb_apply]
  congr 1
  ring

/-! ### Shifted kernels -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.B_FourThm
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
/-!
# WP-B, part 8: the Fourier expansion at `∞` — statements

For a genuine section `Φ`, `Re s > 2`, `ν ∈ R`, a depth `M` valid for `(Φ, ν)`
(`ValidDepth hG Φ ν M`), and any fundamental cell `D` of finite volume of the translation
lattice `Λ_M = transLat 𝔪 M = emb (R ∩ 𝔩_M) ⊂ ℂ^r`:

* `fourier_coeff` (all `ν`), `fourier_coeff_ne_zero` (`ν ≠ 0`), `const_term` (`ν = 0`).

Normalizations: `chiInf ν x = conj e_∞(νx)`, `e_∞(x) = ∏_w archChar (-x_w)` (so
`e_∞ = exp(-2πi Tr)` on `F`); `dx` is Lebesgue measure on `ℂ^r = (ℝ²)^r`;
`Winf s ν v = ∏_w jacquet s (-σ_w ν) v_w`; `vol 𝔪 M = ∏_{v ∣ 𝔪} q_v^{-M}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate Pointwise
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

theorem continuous_mk_x (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) :
    Continuous fun x : InfinitePlace F → ℂ => X.mk x v hv := by
  refine continuous_pi fun w => ?_
  exact Continuous.subtype_mk ((continuous_apply w).prodMk continuous_const) _

/-! ### Characters on the cell -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.X2_Chart
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol
/-! # WP-X2, file 1: the logarithmic chart of `X = (H³)^r`

`chart F : (InfinitePlace F → ℂ × ℝ) ≃ₜ X F`, `(x_w, t_w)_w ↦ (x_w, exp t_w)_w`.  In this chart
`X.vol F` is Lebesgue measure with the smooth density `rho y = exp (-2 ∑_w t_w)`
(`measurePreserving_chart`).  All calculus on `X` is done in this chart: a function on `X` is
smooth iff its pull-back to the vector space `Coord F` is.

Also: Tonelli for products of functions of one coordinate on a finite product
(`lintegral_fintype_prod_eq_prod`) and `pi_withDensity`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

/-! ### Products of densities -/

section PiDensity

set_option backward.isDefEq.respectTransparency false in
theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      calc
        _ = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫⁻ x, f 0 x ∂μ 0)
            * ∏ i : Fin n, ∫⁻ (x : E (Fin.succ i)), f (Fin.succ i) x ∂(μ i.succ) := by
          rw [← n_ih (fun i => f i.succ) (fun i => hf i.succ),
            ← lintegral_prod_mul (hf 0).aemeasurable]
          exact (Finset.measurable_prod _ fun i _ =>
            (hf i.succ).comp (measurable_pi_apply i)).aemeasurable
        _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

variable {ι : Type*} [Fintype ι]

/-- Tonelli on a finite product, for a product of functions of one coordinate each. -/
theorem lintegral_fintype_prod_eq_prod {E : ι → Type*} (f : (i : ι) → E i → ℝ≥0∞)
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  rw [lintegral_fin_nat_prod_eq_prod (fun i => f (e i)) (fun i => hf (e i))]

/-- A product of measures with densities is the product measure with the product density. -/
theorem pi_withDensity {α : ι → Type*} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] (f : ∀ i, α i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have h : ∀ x : ∀ i, α i, (Set.pi univ s).indicator (fun x => ∏ i, f i (x i)) x =
      ∏ i, (s i).indicator (f i) (x i) := by
    intro x
    by_cases hx : x ∈ Set.pi univ s
    · rw [indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ => (indicator_of_mem (hx i (mem_univ i)) _).symm
    · rw [indicator_of_notMem hx]
      simp only [mem_pi, mem_univ, forall_true_left, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)).symm
  simp_rw [h]
  rw [lintegral_fintype_prod_eq_prod _ (fun i => (hf i).indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), lintegral_indicator (hs i)]

end PiDensity

/-! ### One factor -/

/-! ### The product -/

variable (F : Type*) [Field F] [NumberField F]

variable {F}

lemma chart_x (y : Coord F) (w : InfinitePlace F) : (chart F y).x w = (y w).1 := rfl
lemma chart_v (y : Coord F) (w : InfinitePlace F) : (chart F y).v w = Real.exp (y w).2 := rfl

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_L2
/-! # WP-X, file 7: `L²` of the quotient and local restriction maps (abstract)

For a partition of unity `η` and a measurable set `B` meeting each orbit at most `m < ∞` times,
pulling back and restricting is a bounded operator
`restrictL2 : L²(G \ α) →L[ℂ] L²(B, μ)` of norm `≤ √m`.  Every functional
`u ↦ ∫_B conj ψ · u` with `ψ ∈ L²(B)` is therefore continuous on `L²(G \ α)`
(`pairingL2`).  This is the continuity of Fourier-coefficient functionals (MATH (C6)).
-/

open scoped ENNReal ComplexConjugate InnerProductSpace
open MeasureTheory Set

set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ] {η : α → ℝ≥0∞}

lemma coeFn_restrictL2 (hη : IsPOU G η) {B : Set α} (hB : MeasurableSet B) {m : ℝ≥0∞}
    (hmtop : m ≠ ⊤) (hm : ∀ a, ∑' g : G, B.indicator (fun _ => (1 : ℝ≥0∞)) (g • a) ≤ m)
    (u : Lp ℂ 2 (quotMeasure G η μ)) :
    restrictL2 hη hB hmtop hm u =ᵐ[μ.restrict B] liftQ u :=
  MemLp.coeFn_toLp (memLp_liftQ_restrict hη hB hmtop hm u)

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Fourier
attribute [-instance] _root_.ArtinKP.B1.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol
attribute [-simp] _root_.ArtinKP.X.chart1_symm_fst _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart1_x _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
/-! # WP-X, file 9: local restriction and coefficient functionals on `L²(Γ\X)`

* `X.vol_box_lt_top`: boxes have finite measure;
* `X.restrictBox Γ n : L²(Γ\X) →L[ℂ] L²(box n)`, bounded;
* `X.coeffFunctional Γ n ψ … : L²(Γ\X) →L[ℂ] ℂ`, `u ↦ ∫_{box n} conj ψ · u`, for bounded measurable
  `ψ`.  The Fourier-coefficient functional `ℓ_{ν,φ}` of MATH (C6) is the case
  `ψ(P) = 1_D(x) · conj(e_∞(-ν x) φ(v))` with `D` a fundamental set of the translation lattice
  and `supp φ` compact (so that `D × supp φ` lies in a box).
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

lemma X.coeFn_restrictBox (Γ : Subgroup (SL(2, 𝓞 F))) (n : ℕ) (u : X.L2 Γ) :
    X.restrictBox Γ n u =ᵐ[(X.vol F).restrict (X.box n)] X.lift Γ u :=
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  coeFn_restrictL2 _ _ _ _ u

lemma X.coeFn_boxLp (n : ℕ) (ψ : X F → ℂ) (hψ : Measurable ψ) (C : ℝ) (hC : ∀ P, ‖ψ P‖ ≤ C) :
    X.boxLp n ψ hψ C hC =ᵐ[(X.vol F).restrict (X.box n)] ψ :=
  MemLp.coeFn_toLp _

theorem X.coeffFunctional_apply (Γ : Subgroup (SL(2, 𝓞 F))) (n : ℕ) (ψ : X F → ℂ)
    (hψ : Measurable ψ) (C : ℝ) (hC : ∀ P, ‖ψ P‖ ≤ C) (u : X.L2 Γ) :
    X.coeffFunctional Γ n ψ hψ C hC u = ∫ P in X.box n, conj (ψ P) * X.lift Γ u P ∂X.vol F := by
  unfold X.coeffFunctional
  rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [X.coeFn_restrictBox Γ n u, X.coeFn_boxLp n ψ hψ C hC] with P h1 h2
  rw [h1, h2]
  simp [mul_comm]

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.C5_Holo
/-! # WP-C5, file 2: bounded holomorphic families are holomorphic into `L²(Γ\X)`

Finite volume is a hypothesis here (`hvol : X.quotVol Γ univ < ⊤`; WP-RC's `quotVol_univ_lt_top`).

* `l2Rep_of_bdd`, `norm_toL2_le`: a bounded measurable `Γ`-invariant function is in `L²(Γ\X)`,
  with norm `≤ vol^{1/2} · sup`.
* `norm_sub_sub_le`: second-order Cauchy/Schwarz estimate
  `|f(z) − f(c) − (z−c) f'(c)| ≤ 4B R⁻² |z−c|²` for `f` holomorphic and bounded by `B` on `B(c,R)`.
* `differentiable_toL2`: if `s ↦ f_s(P)` is entire for every `P` and `f` is bounded on
  `ball × X` near every `s₀`, then `s ↦ [f_s] ∈ L²(Γ\X)` is entire.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C5

open ArtinKP.X

noncomputable section

/-- Second-order estimate for a bounded holomorphic function on a disc. -/
lemma norm_sub_sub_le {f : ℂ → ℂ} {c : ℂ} {R B : ℝ} (hR : 0 < R)
    (hd : DifferentiableOn ℂ f (ball c R)) (hB : ∀ z ∈ ball c R, ‖f z‖ ≤ B) {z : ℂ}
    (hz : z ∈ ball c R) :
    ‖f z - f c - (z - c) * deriv f c‖ ≤ 4 * B / R ^ 2 * ‖z - c‖ ^ 2 := by
  have hc : c ∈ ball c R := mem_ball_self hR
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB c hc)
  have hm1 : MapsTo f (ball c R) (closedBall (f c) (2 * B)) := fun w hw => by
    rw [mem_closedBall, dist_eq_norm]
    calc ‖f w - f c‖ ≤ ‖f w‖ + ‖f c‖ := norm_sub_le _ _
      _ ≤ 2 * B := by linarith [hB w hw, hB c hc]
  have hD : ∀ w ∈ ball c R, ‖dslope f c w‖ ≤ 2 * B / R := fun w hw =>
    Complex.norm_dslope_le_div_of_mapsTo_ball hd hm1 hw
  have hdD : DifferentiableOn ℂ (dslope f c) (ball c R) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds c hR)).mpr hd
  have hm2 : MapsTo (dslope f c) (ball c R) (closedBall (dslope f c c) (4 * B / R)) :=
    fun w hw => by
      rw [mem_closedBall, dist_eq_norm]
      calc ‖dslope f c w - dslope f c c‖ ≤ ‖dslope f c w‖ + ‖dslope f c c‖ := norm_sub_le _ _
        _ ≤ 2 * B / R + 2 * B / R := add_le_add (hD w hw) (hD c hc)
        _ = 4 * B / R := by ring
  have h2 := Complex.dist_le_div_mul_dist_of_mapsTo_ball hdD hm2 hz
  rw [dist_eq_norm, dist_eq_norm, dslope_same] at h2
  rcases eq_or_ne z c with rfl | hne
  · simp
  · have hzc : z - c ≠ 0 := sub_ne_zero.mpr hne
    have e : f z - f c - (z - c) * deriv f c = (z - c) * (dslope f c z - deriv f c) := by
      rw [dslope_of_ne _ hne, slope_def_module, smul_eq_mul]
      field_simp
    rw [e, norm_mul]
    calc ‖z - c‖ * ‖dslope f c z - deriv f c‖ ≤ ‖z - c‖ * (4 * B / R / R * ‖z - c‖) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = 4 * B / R ^ 2 * ‖z - c‖ ^ 2 := by ring

/-- The derivative of a bounded holomorphic function at the centre of a disc. -/
lemma norm_deriv_le {f : ℂ → ℂ} {c : ℂ} {R B : ℝ} (hR : 0 < R)
    (hd : DifferentiableOn ℂ f (ball c R)) (hB : ∀ z ∈ ball c R, ‖f z‖ ≤ B) :
    ‖deriv f c‖ ≤ 2 * B / R := by
  have hc : c ∈ ball c R := mem_ball_self hR
  have hm1 : MapsTo f (ball c R) (closedBall (f c) (2 * B)) := fun w hw => by
    rw [mem_closedBall, dist_eq_norm]
    calc ‖f w - f c‖ ≤ ‖f w‖ + ‖f c‖ := norm_sub_le _ _
      _ ≤ 2 * B := by linarith [hB w hw, hB c hc]
  have := Complex.norm_dslope_le_div_of_mapsTo_ball hd hm1 hc
  rwa [dslope_same] at this

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.X2_Prod
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol
/-! # WP-X2, file 9: product coordinates `(x, v)` on `X` (stub S3 of WP-X)

`X.measurePreserving_xv`: the map `P ↦ (P.x, P.v) : X F → (ι → ℂ) × (ι → ℝ)` carries `X.vol F`
to `volume.prod (X.nuV F)`, `X.nuV F = ∏_w dv_w / v_w³` on `(0,∞)^ι`.  Hence integrals over `X`
and over strips `{x ∈ D}` are iterated integrals (`X.lintegral_xv`, `X.setLIntegral_strip`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

lemma amb_eq_prod : amb = (volume : Measure ℂ).prod nu1 := by
  have h2 : (volume : Measure ℂ).prod ((volume : Measure ℝ).restrict (Ioi 0)) =
      (volume : Measure (ℂ × ℝ)).restrict upper := by
    have hu : upper = (univ : Set ℂ) ×ˢ Ioi (0 : ℝ) := by
      ext p; simp [upper]
    rw [hu, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  unfold nu1
  rw [prod_withDensity_right (by fun_prop), h2]
  rfl

lemma measurePreserving_coe : MeasurePreserving H3.coe H3.vol ((volume : Measure ℂ).prod nu1) :=
  ⟨H3.measurableEmbedding_coe.measurable, map_val_vol.trans amb_eq_prod⟩

variable (F : Type*) [Field F] [NumberField F]

lemma X.nuV_eq : X.nuV F =
    (Measure.pi fun _ : InfinitePlace F => (volume : Measure ℝ).restrict (Ioi 0)).withDensity
      (fun v => ∏ w, ENNReal.ofReal ((v w ^ 3)⁻¹)) := by
  unfold X.nuV nu1
  exact pi_withDensity _ _ (fun _ => by fun_prop)

/-- **Product coordinates**: `P ↦ (x, v)` carries the invariant measure to
`dx ⊗ ∏_w dv_w / v_w³`. -/
theorem X.measurePreserving_xv :
    MeasurePreserving (fun P : X F => (P.x, P.v)) (X.vol F)
      ((volume : Measure (InfinitePlace F → ℂ)).prod (X.nuV F)) := by
  have h2 : MeasurePreserving (fun (P : X F) w => H3.coe (P w)) (X.vol F)
      (Measure.pi fun _ : InfinitePlace F => (volume : Measure ℂ).prod nu1) :=
    measurePreserving_pi (fun _ => H3.vol) (fun _ => (volume : Measure ℂ).prod nu1)
      (fun _ => measurePreserving_coe)
  have h3 := measurePreserving_arrowProdEquivProdArrow ℂ ℝ (InfinitePlace F)
    (fun _ => (volume : Measure ℂ)) (fun _ => nu1)
  exact h3.comp h2

variable {F}

lemma X.measurable_xv : Measurable fun P : X F => (P.x, P.v) :=
  (X.measurePreserving_xv F).measurable

/-- Integrals over `X` in product coordinates. -/
theorem X.lintegral_xv {f : (InfinitePlace F → ℂ) × (InfinitePlace F → ℝ) → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ P, f (P.x, P.v) ∂X.vol F = ∫⁻ x, ∫⁻ v, f (x, v) ∂X.nuV F := by
  rw [← lintegral_prod _ hf.aemeasurable]
  exact (X.measurePreserving_xv F).lintegral_comp hf

/-- Integrals over a strip `{x ∈ D}` are iterated integrals `∫_D dx ∫ ∏ dv/v³`. -/
theorem X.setLIntegral_strip {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D)
    {f : (InfinitePlace F → ℂ) × (InfinitePlace F → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ P in (X.x ⁻¹' D : Set (X F)), f (P.x, P.v) ∂X.vol F =
      ∫⁻ x in D, ∫⁻ v, f (x, v) ∂X.nuV F := by
  have hm : MeasurableSet (X.x ⁻¹' D : Set (X F)) :=
    (measurable_fst.comp X.measurable_xv) hD
  rw [← lintegral_indicator hm, ← lintegral_indicator hD]
  have h1 : ∀ P : X F, (X.x ⁻¹' D : Set (X F)).indicator (fun P => f (P.x, P.v)) P =
      (fun p : (InfinitePlace F → ℂ) × (InfinitePlace F → ℝ) =>
        D.indicator (fun _ => (1 : ℝ≥0∞)) p.1 * f p) (P.x, P.v) := by
    intro P
    by_cases h : P.x ∈ D
    · simp [h]
    · simp [h]
  simp_rw [h1]
  refine (X.lintegral_xv (f := fun p => D.indicator (fun _ => (1 : ℝ≥0∞)) p.1 * f p)
    (((measurable_const.indicator hD).comp measurable_fst).mul hf)).trans ?_
  refine lintegral_congr fun x => ?_
  by_cases h : x ∈ D
  · simp [h]
  · simp [h]

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.RF_Strip
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol
/-!
# WP-RF, part 3: Fourier uniqueness on a strip of `X` (core of stub S1 (b))

Product coordinates `P ↦ (x, v) : X F → XV F = (ι → ℂ) × (ι → ℝ)` carry `X.vol` to Lebesgue
measure with density `dens v = ∏_w v_w⁻³` on `v > 0` (`map_xv`).  For a basis `bV` of `ι → ℂ`
(the lattice basis of the translations) and `n : ℕ`, the box
`{x ∈ cell bV} × [1/(n+1), n+1]^ι` lies in the cell of the basis `bE bV n = bV ⊕ (n+2)·e_w` of
`XV F`, whose characters are `chi bV m x · phiK n k v`.  Hence (`RF_Torus.ae_eq_zero_of_coeff`):

`measure_ne_zero_null`: a function on `X`, square integrable on that box, all of whose
coefficients against `chi bV m (x) · phiK n k (v)` over the box vanish, is `0` a.e. on the box.
No Fubini and no slicing: the `v`-directions are treated as further circle directions.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace ArtinKP.RF

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-! ### The density of `X.vol` in product coordinates -/

lemma measurableSet_posSet : MeasurableSet (posSet F) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioi

lemma measurable_dens : Measurable (dens : (InfinitePlace F → ℝ) → ℝ≥0∞) := by
  unfold dens
  refine Measurable.indicator ?_ measurableSet_posSet
  exact Finset.measurable_prod _ fun w _ => by fun_prop

lemma nuV_eq_withDensity : X.nuV F = (volume : Measure (InfinitePlace F → ℝ)).withDensity dens := by
  rw [X.nuV_eq]
  have h1 : (Measure.pi fun _ : InfinitePlace F => (volume : Measure ℝ).restrict (Ioi 0))
      = (volume : Measure (InfinitePlace F → ℝ)).restrict (posSet F) :=
    (Measure.restrict_pi_pi (fun _ : InfinitePlace F => (volume : Measure ℝ))
      (fun _ => Ioi (0 : ℝ))).symm
  rw [h1, ← withDensity_indicator measurableSet_posSet]
  rfl

lemma ofXV_toXV (P : X F) : ofXV (toXV P) = P := (chart F).apply_symm_apply P

lemma measurable_ofXV : Measurable (ofXV : XV F → X F) := by
  refine (chart F).continuous.measurable.comp (measurable_pi_lambda _ fun w => ?_)
  exact ((measurable_pi_apply w).comp measurable_fst).prodMk
    (Real.measurable_log.comp ((measurable_pi_apply w).comp measurable_snd))

/-! ### Boxes in `v` -/

lemma measurableSet_vBox (n : ℕ) : MeasurableSet (vBox F n) := by
  have : vBox F n = ⋂ w, {v : InfinitePlace F → ℝ | 1 / ((n : ℝ) + 1) ≤ v w} ∩
      {v | v w ≤ (n : ℝ) + 1} := by
    ext v; simp [vBox, forall_and]
  rw [this]
  exact MeasurableSet.iInter fun w =>
    (measurableSet_le measurable_const (measurable_pi_apply w)).inter
      (measurableSet_le (measurable_pi_apply w) measurable_const)

lemma vBox_subset_posSet (n : ℕ) : vBox F n ⊆ posSet F := fun v hv w _ =>
  lt_of_lt_of_le (by positivity) (hv w).1

lemma dens_ne_zero {n : ℕ} {v : InfinitePlace F → ℝ} (hv : v ∈ vBox F n) : dens v ≠ 0 := by
  unfold dens
  rw [indicator_of_mem (vBox_subset_posSet n hv)]
  refine Finset.prod_ne_zero_iff.mpr fun w _ => ?_
  have h0 : 0 < v w := vBox_subset_posSet n hv w (mem_univ w)
  exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'

/-! ### The basis of `XV F` adapted to a box -/

end

end ArtinKP.RF
end

section
-- module Solutions.Artin.KP.RF_Fourier
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup
/-!
# WP-RF, part 4: Fourier series along `x` on `Γ\X` (stub S1 of WP-X)

Setting of WP-X "Remaining stubs": `F` totally complex, `Γ ≤ SL(2,𝓞_F)` containing the
translations `n(β)`, `β ∈ 𝔫`; `Λ = {GammaN.shift γ}` the translation lattice in `ι → ℂ`;

* `pair ν x = Σ_w Re(ν_w x_w)`, `eChar ν x = exp(2πi · pair ν x)`,
  `dualLat Γ = {ν | pair ν λ ∈ ℤ for all λ ∈ Λ}`;
* `stripFn D ν φ P = 1_D(P.x) · e_ν(P.x) · φ(P.v)`, the function `ψ` of
  `X.coeffFunctional Γ n ψ …` for the `(ν, φ)`-Fourier coefficient;
* `exists_latBasis`: a basis of `ι → ℂ` whose `ℤ`-span is `Λ`; the characters `chi bV m` of
  `RF_Torus` are the `eChar ν`, `ν ∈ dualLat Γ` (`exists_dual_of_chi`);
* **`eq_zero_of_coeff`** (S1 (b)): `u : X.L2 Γ` with all coefficient functionals zero is zero;
* `ae_eq_zero_of_strip`: the same for any measurable `GammaN Γ`-invariant function which is
  square integrable on boxes.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace ArtinKP.RF

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-! ### The pairing and the characters -/

/-! ### A basis of the translation lattice -/

lemma mem_box_iff (n : ℕ) (P : X F) :
    P ∈ (X.box n : Set (X F)) ↔ (∀ w, ‖P.x w‖ ≤ n) ∧ P.v ∈ vBox F n := by
  simp only [X.box, H3.box, vBox, mem_ofPred_eq, X.x, X.v]
  exact forall_and

end

end ArtinKP.RF
end

section
-- module Solutions.Artin.KP.N_Shape
/-! # WP-N, file 2: the shape of the constant term of `E_Ψ` at `∞` for `Re s > 2` (MATH2 §2.1(b))

* `Cell Γ D n₀`: `D` is a measurable fundamental domain of the translation lattice of `Γ`, contained
  in `{‖x_w‖ ≤ n₀}`.  `Cell.of_hfund` converts from the form used by WP-X/WP-RF (`hfund`);
  `exists_cell` gives one for every `Γ` of finite index.
* `cf D n φ f = ∫_{box n} conj (1_D(x) φ(v)) f`: the constant-term functional (it is
  `X.coeffFunctional Γ n (RF.stripFn D 0 φ) …` on `L²(Γ\X)`, `coeffFunctional_eq_cf`).
* `mD D Ψ s = vol(D)⁻¹ ∫_D tail Ψ s (x, 1) dx`: the coefficient of `ht^{2−s}`.
* **`cf_eis`**: for `Re s > 2`, `n ≥ n₀`,
  `cf D n φ (E_Ψ(·,s)) = Ψ_s(0,1) · cf D n φ (ht^s) + mD D Ψ s · cf D n φ (ht^{2−s})`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### Cells -/

/-! ### The constant-term functional -/

lemma eChar_zero (x : InfinitePlace F → ℂ) : eChar 0 x = 1 := by
  simp [eChar, pair]

lemma stripFn_zero (D : Set (InfinitePlace F → ℂ)) (φ : (InfinitePlace F → ℝ) → ℂ) (P : X F) :
    stripFn D 0 φ P = D.indicator (fun _ => (1 : ℂ)) P.x * φ P.v := by
  rw [stripFn, eChar_zero, one_mul]

section lin

variable {D : Set (InfinitePlace F → ℂ)} {n : ℕ} {φ : (InfinitePlace F → ℝ) → ℂ}

lemma cf_integrable (hD : MeasurableSet D) (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1)
    {f : X F → ℂ} (hf : IntegrableOn f (X.box n) (X.vol F)) :
    IntegrableOn (fun P => conj (stripFn D 0 φ P) * f P) (X.box n) (X.vol F) := by
  refine Integrable.bdd_mul (c := 1) hf
    (Complex.continuous_conj.measurable.comp (measurable_stripFn hD 0 hφ)).aestronglyMeasurable ?_
  exact Eventually.of_forall fun P => by
    rw [RCLike.norm_conj]; exact norm_stripFn_le D 0 hφ1 P

lemma cf_sub (hD : MeasurableSet D) (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1)
    {f g : X F → ℂ} (hf : IntegrableOn f (X.box n) (X.vol F))
    (hg : IntegrableOn g (X.box n) (X.vol F)) :
    cf D n φ (fun P => f P - g P) = cf D n φ f - cf D n φ g := by
  unfold cf
  rw [← integral_sub (cf_integrable hD hφ hφ1 hf) (cf_integrable hD hφ hφ1 hg)]
  exact integral_congr_ae (Eventually.of_forall fun P => by ring)

lemma cf_const_mul (c : ℂ) (f : X F → ℂ) :
    cf D n φ (fun P => c * f P) = c * cf D n φ f := by
  unfold cf
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun P => by ring)

end lin

/-! ### Fubini: a function with vanishing `x`-integrals over `D` is killed by `cf` -/

lemma ofXV_eq_mk (x : InfinitePlace F → ℂ) {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) :
    ofXV (x, v) = X.mk x v hv := by
  refine X.ext' (funext fun w => ?_) (funext fun w => ?_)
  · simp [ofXV, chart_x]
  · simp [ofXV, chart_v, Real.exp_log (hv w)]

theorem cf_eq_zero_of_fibers {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D) {n : ℕ}
    (hn : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) {φ : (InfinitePlace F → ℝ) → ℂ} (hφ : Measurable φ)
    (hφ1 : ∀ v, ‖φ v‖ ≤ 1) {R : X F → ℂ} (hR : Measurable R)
    (hint : IntegrableOn R (X.box n) (X.vol F))
    (h0 : ∀ (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w), ∫ x in D, R (X.mk x v hv) = 0) :
    cf D n φ R = 0 := by
  classical
  set G : X F → ℂ := (X.box n : Set (X F)).indicator
    (fun P => conj (stripFn D 0 φ P) * R P) with hG
  have hGm : Measurable G :=
    ((Complex.continuous_conj.measurable.comp (measurable_stripFn hD 0 hφ)).mul hR).indicator
      (X.measurableSet_box n)
  have hGint : Integrable G (X.vol F) :=
    (cf_integrable hD hφ hφ1 hint).integrable_indicator (X.measurableSet_box n)
  set H : XV F → ℂ := fun p => if p.2 ∈ vBox F n then G (ofXV p) else 0 with hH
  have hHm : Measurable H :=
    Measurable.ite (measurable_snd (measurableSet_vBox n)) (hGm.comp measurable_ofXV)
      measurable_const
  have hmp := X.measurePreserving_xv (F := F)
  have hGH : ∀ P : X F, H (P.x, P.v) = G P := by
    intro P
    have hP : ofXV (P.x, P.v) = P := ofXV_toXV P
    simp only [hH, hP]
    split_ifs with hv
    · rfl
    · rw [hG, indicator_of_notMem]
      intro hbox
      exact hv ((mem_box_iff n P).mp hbox).2
  have e1 : cf D n φ R = ∫ p, H p ∂((volume : Measure (InfinitePlace F → ℂ)).prod (X.nuV F)) := by
    unfold cf
    rw [← integral_indicator (X.measurableSet_box n), ← hmp.map_eq,
      integral_map hmp.aemeasurable hHm.aestronglyMeasurable]
    exact integral_congr_ae (Eventually.of_forall fun P => (hGH P).symm)
  have hHint : Integrable H ((volume : Measure (InfinitePlace F → ℂ)).prod (X.nuV F)) := by
    rw [← hmp.integrable_comp hHm.aestronglyMeasurable]
    exact hGint.congr (Eventually.of_forall fun P => (hGH P).symm)
  rw [e1, integral_prod_symm H hHint]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun v => ?_)
  change ∫ x, H (x, v) = 0
  by_cases hv : v ∈ vBox F n
  · have hpos : ∀ w, 0 < v w := fun w => vBox_subset_posSet n hv w (mem_univ _)
    have h1 : ∀ x : InfinitePlace F → ℂ,
        H (x, v) = D.indicator (fun x => conj (φ v) * R (X.mk x v hpos)) x := by
      intro x
      simp only [hH, if_pos hv, ofXV_eq_mk x hpos, hG]
      by_cases hx : x ∈ D
      · have hb : X.mk x v hpos ∈ (X.box n : Set (X F)) := by
          rw [mem_box_iff]
          exact ⟨by simpa using hn x hx, by simpa using hv⟩
        rw [indicator_of_mem hb, indicator_of_mem hx, stripFn_zero]
        simp [indicator_of_mem hx]
      · rw [indicator_of_notMem hx]
        by_cases hb : X.mk x v hpos ∈ (X.box n : Set (X F))
        · rw [indicator_of_mem hb, stripFn_zero]
          simp [indicator_of_notMem hx]
        · rw [indicator_of_notMem hb]
    simp only [h1]
    rw [integral_indicator hD, integral_const_mul, h0 v hpos, mul_zero]
  · simp [hH, if_neg hv]

/-! ### The shape -/

lemma isCompact_box (n : ℕ) : IsCompact (X.box n : Set (X F)) :=
  isCompact_siegelBox (F := F) (m := 1 / ((n : ℝ) + 1)) (M := (n : ℝ) + 1) (B := n)
    (by positivity)

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.N_Cont
/-! # WP-N, file 3: coefficients of `θ_Ψ` from continuations (MATH2 §2.1(c),(d); item 5)

* `differentiableAt_setIntegral`: a bounded holomorphic family integrates to a holomorphic function
  over a set of finite measure.
* `hInt Ψ n ψ s = ∫_{box n} conj ψ · h_s` is entire (`differentiable_hInt`).
* **`coeff_theta_of_continuation`** (all frequencies): if `a` is holomorphic on `E.slit`, equals
  `∫_{box n} conj ψ · E_Ψ(·, s)` for `Re s > 2`, and `(s_t − s₀) a(s_t) → r` along C5's ray, then
  `∫_{box n} conj ψ · θ_Ψ = r`.
* **`cf_theta_of_continuation`** (frequency `0`, MATH2 §2.1(d)): if `m'` is holomorphic on `E.slit`,
  equals `mD D Ψ` for `Re s > 2` and `(s_t − s₀) m'(s_t) → z`, then
  `cf D n φ (θ_Ψ) = z · cf D n φ (ht^{2/3})` for all `(n, φ)`.

`EisEigen Ψ s` (owner WP-RF) enters as the hypothesis `hE : ∀ s, 2 < s.re → EisEigen Ψ s`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF

noncomputable section

/-! ### Holomorphic dependence of integrals on a parameter -/

/-- A family `f s`, measurable in `a`, holomorphic in `s` on a disc and bounded there uniformly
on `K`, has a holomorphic integral over `K` (`μ K < ∞`). -/
theorem differentiableAt_setIntegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {K : Set α} (hK : MeasurableSet K) (hμ : μ K ≠ ⊤) {f : ℂ → α → ℂ} {s₀ : ℂ} {R B₀ : ℝ}
    (hR : 0 < R) (hmeas : ∀ s ∈ ball s₀ R, Measurable (f s))
    (hdiff : ∀ a ∈ K, DifferentiableOn ℂ (fun s => f s a) (ball s₀ R))
    (hB₀ : ∀ s ∈ ball s₀ R, ∀ a ∈ K, ‖f s a‖ ≤ B₀) :
    DifferentiableAt ℂ (fun s => ∫ a in K, f s a ∂μ) s₀ := by
  have : IsFiniteMeasure (μ.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]; exact hμ.lt_top⟩
  have hs₀ : s₀ ∈ ball s₀ R := mem_ball_self hR
  set B : ℝ := max B₀ 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  have hB : ∀ s ∈ ball s₀ R, ∀ a ∈ K, ‖f s a‖ ≤ B := fun s hs a ha =>
    (hB₀ s hs a ha).trans (le_max_left _ _)
  set g : α → ℂ := fun a => deriv (fun s => f s a) s₀ with hg
  have hgb : ∀ a ∈ K, ‖g a‖ ≤ 2 * B / R := fun a ha =>
    C5.norm_deriv_le hR (hdiff a ha) fun z hz => hB z hz a ha
  -- measurability of the derivative on `K`
  set k : ℕ → ℂ := fun n => ((R / 2 : ℝ) : ℂ) / ((n : ℂ) + 1) with hk
  have hk0 : ∀ n, k n ≠ 0 := fun n => by
    rw [hk]
    exact div_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) (Nat.cast_add_one_ne_zero n)
  have hkR : ∀ n, s₀ + k n ∈ ball s₀ R := fun n => by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hk, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < R / 2)]
    have h1 : (1 : ℝ) ≤ ‖((n : ℂ) + 1)‖ := by
      have : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    calc R / 2 / ‖((n : ℂ) + 1)‖ ≤ R / 2 / 1 :=
          div_le_div_of_nonneg_left (by positivity) one_pos h1
      _ < R := by linarith
  have hkt : Tendsto k atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)).const_mul (((R / 2 : ℝ) : ℂ))
    simpa [hk, div_eq_mul_inv] using this
  have hgK : Measurable (K.indicator g) := by
    refine measurable_of_tendsto_metrizable
      (f := fun n => K.indicator fun a => (k n)⁻¹ * (f (s₀ + k n) a - f s₀ a))
      (fun n => (((hmeas _ (hkR n)).sub (hmeas _ hs₀)).const_mul _).indicator hK) ?_
    rw [tendsto_pi_nhds]
    intro a
    by_cases ha : a ∈ K
    · simp only [indicator_of_mem ha]
      have h1 := ((hdiff a ha).differentiableAt (ball_mem_nhds s₀ hR)).hasDerivAt.tendsto_slope
      have h2 : Tendsto (fun n => s₀ + k n) atTop (𝓝[≠] s₀) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
        · simpa using (tendsto_const_nhds (x := s₀)).add hkt
        · simpa using hk0 n
      refine (h1.comp h2).congr fun n => ?_
      simp [slope_def_module]
    · simp only [indicator_of_notMem ha]
      exact tendsto_const_nhds
  have hgint : Integrable g (μ.restrict K) :=
    Integrable.of_bound (hgK.aestronglyMeasurable.congr (indicator_ae_eq_restrict hK))
      (2 * B / R) (ae_restrict_of_forall_mem hK hgb)
  have hfint : ∀ s ∈ ball s₀ R, Integrable (f s) (μ.restrict K) := fun s hs =>
    Integrable.of_bound (hmeas s hs).aestronglyMeasurable B
      (ae_restrict_of_forall_mem hK (hB s hs))
  refine (HasDerivAt.differentiableAt (f' := ∫ a in K, g a ∂μ) ?_)
  rw [hasDerivAt_iff_isLittleO]
  set V : ℝ := (μ.restrict K).real univ with hV
  have key : ∀ z ∈ ball s₀ R,
      ‖(∫ a in K, f z a ∂μ) - (∫ a in K, f s₀ a ∂μ) - (z - s₀) • ∫ a in K, g a ∂μ‖ ≤
        (4 * B / R ^ 2) * V * ‖z - s₀‖ ^ 2 := by
    intro z hz
    have e : (∫ a in K, f z a ∂μ) - (∫ a in K, f s₀ a ∂μ) - (z - s₀) • ∫ a in K, g a ∂μ
        = ∫ a in K, (f z a - f s₀ a - (z - s₀) * g a) ∂μ := by
      have i1 : Integrable (fun a => f z a - f s₀ a) (μ.restrict K) :=
        (hfint z hz).sub (hfint s₀ hs₀)
      have i2 : Integrable (fun a => (z - s₀) * g a) (μ.restrict K) := hgint.const_mul _
      rw [integral_sub i1 i2, integral_sub (hfint z hz) (hfint s₀ hs₀), integral_const_mul,
        smul_eq_mul]
    rw [e]
    have hb' : ∀ a ∈ K, ‖f z a - f s₀ a - (z - s₀) * g a‖ ≤ 4 * B / R ^ 2 * ‖z - s₀‖ ^ 2 :=
      fun a ha => C5.norm_sub_sub_le hR (hdiff a ha) (fun w hw => hB w hw a ha) hz
    have := norm_integral_le_of_norm_le_const (μ := μ.restrict K)
      (ae_restrict_of_forall_mem hK hb')
    calc _ ≤ 4 * B / R ^ 2 * ‖z - s₀‖ ^ 2 * V := this
      _ = _ := by ring
  have hO : (fun z => (∫ a in K, f z a ∂μ) - (∫ a in K, f s₀ a ∂μ)
      - (z - s₀) • ∫ a in K, g a ∂μ) =O[𝓝 s₀] fun z => ‖z - s₀‖ ^ 2 := by
    refine Asymptotics.IsBigO.of_bound ((4 * B / R ^ 2) * V) ?_
    filter_upwards [ball_mem_nhds s₀ hR] with z hz
    rw [norm_pow, norm_norm]
    exact key z hz
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub s₀ one_lt_two)

/-! ### The ray and the slit -/

lemma isOpen_slit : IsOpen E.slit := by
  have h : E.slit = {s : ℂ | 1 < s.re} ∩ ({s : ℂ | s.im ≠ 0} ∪ {s : ℂ | 2 < s.re}) := by
    ext s
    simp only [E.slit, mem_ofPred_eq, mem_inter_iff, mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by by_cases h : s.im = 0; exacts [Or.inr (h2 h), Or.inl h]⟩
    · rintro ⟨h1, h2 | h2⟩
      · exact ⟨h1, fun h => absurd h h2⟩
      · exact ⟨h1, fun _ => h2⟩
  rw [h]
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_ne_fun Complex.continuous_im continuous_const).union
      (isOpen_lt continuous_const Complex.continuous_re))

lemma ray_mem_slit {t : ℝ} (ht : 0 < t) : ray t ∈ E.slit := by
  have hre : (ray t).re = 4 / 3 + t := by
    simp only [ray, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.I_re, Complex.div_ofNat_re, Complex.re_ofNat]
    ring
  have him : (ray t).im = t := by
    simp only [ray, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_im, Complex.I_im, Complex.div_ofNat_im, Complex.im_ofNat]
    ring
  exact ⟨by rw [hre]; linarith, fun h => by rw [him] at h; exact absurd h ht.ne'⟩

lemma continuous_ray : Continuous ray := by unfold ray; fun_prop

lemma tendsto_ray : Tendsto ray (𝓝[>] 0) (𝓝 (4 / 3)) := by
  have h := continuous_ray.tendsto 0
  have h0 : ray 0 = 4 / 3 := by simp [ray]
  rw [h0] at h
  exact h.mono_left nhdsWithin_le_nhds

/-! ### The cut-off part against a bounded test function -/

/-! ### Coefficients of `θ_Ψ` from a continuation (all test functions) -/

/-! ### Frequency `0`: the residue of the `ht^{2−s}`-coefficient -/

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.T_Arch
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

theorem continuous_sFK {s : ℂ} (hs : 1 < s.re) : Continuous (sourceFourierKernel s) := by
  unfold sourceFourierKernel
  refine continuous_of_dominated (bound := fun z => ‖hyperbolicKernel s z‖) (fun ξ => ?_)
    (fun ξ => ?_) (hyperbolicKernel_integrable s hs).norm ?_
  · have hchar : Continuous (fun z : ℂ => archChar (-ξ * z)) :=
      K.continuous_archChar.comp (by fun_prop)
    exact ((continuous_hyperbolicKernel s).mul hchar).aestronglyMeasurable
  · exact Eventually.of_forall fun z => by rw [norm_mul, archChar_norm, mul_one]
  · exact Eventually.of_forall fun z =>
      continuous_const.mul (K.continuous_archChar.comp (by fun_prop))

theorem norm_sFK_le {s : ℂ} (hs : 1 < s.re) (ξ : ℂ) :
    ‖sourceFourierKernel s ξ‖ ≤ Real.pi / (s.re - 1) := by
  have h1 : ‖sourceFourierKernel s ξ‖ ≤ ∫ z : ℂ, ‖hyperbolicKernel s z‖ := by
    unfold sourceFourierKernel
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext z; rw [norm_mul, archChar_norm, mul_one]
  have h2 : ∀ z : ℂ, ‖hyperbolicKernel s z‖ = (1 + ‖z‖ ^ 2 : ℝ) ^ (-s.re) := by
    intro z; unfold hyperbolicKernel
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]; simp
  have h3 : ((∫ z : ℂ, (1 + ‖z‖ ^ 2 : ℝ) ^ (-s.re) : ℝ) : ℂ)
      = (Real.pi : ℂ) / ((s.re : ℂ) - 1) := by
    rw [← integral_hyperbolicKernel (s.re : ℂ) (by simpa using hs), ← integral_complex_ofReal]
    congr 1; funext z; unfold hyperbolicKernel
    rw [Complex.ofReal_cpow (by positivity)]; simp
  have h4 : ∫ z : ℂ, (1 + ‖z‖ ^ 2 : ℝ) ^ (-s.re) = Real.pi / (s.re - 1) := by
    exact_mod_cast h3
  simp only [h2] at h1
  rw [h4] at h1
  exact h1

theorem sFK_zero_ne {s : ℂ} (hs : 1 < s.re) : sourceFourierKernel s 0 ≠ 0 := by
  rw [sourceFourierKernel_zero s hs]
  refine div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) fun h => ?_
  have := congrArg Complex.re h
  simp at this
  linarith

/-- Near frequency `0` the kernel does not vanish. -/
theorem exists_sFK_ne_zero {s : ℂ} (hs : 1 < s.re) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ξ : ℂ, ‖ξ‖ < ε → sourceFourierKernel s ξ ≠ 0 := by
  have h := (continuous_sFK hs).continuousAt.eventually_ne (sFK_zero_ne hs)
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff.mp h
  exact ⟨ε, hε, fun ξ hξ => hb (by simpa using hξ)⟩

lemma rpow_le_of_mem {a v e E : ℝ} (ha : 1 ≤ a) (hv1 : 1 / a ≤ v) (hv2 : v ≤ a) (he : |e| ≤ E) :
    v ^ e ≤ a ^ E := by
  have ha0 : 0 < a := by linarith
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) hv1
  have h1 : v ^ e ≤ a ^ |e| := by
    rcases le_total 0 e with h | h
    · rw [abs_of_nonneg h]
      exact Real.rpow_le_rpow hv0.le hv2 h
    · rw [abs_of_nonpos h]
      have e1 : v ^ e = (v⁻¹) ^ (-e) := by
        rw [Real.inv_rpow hv0.le, ← Real.rpow_neg hv0.le, neg_neg]
      rw [e1]
      refine Real.rpow_le_rpow (by positivity) ?_ (by linarith)
      rw [inv_le_comm₀ hv0 ha0]
      simpa [one_div] using hv1
  exact h1.trans (Real.rpow_le_rpow_of_exponent_le ha he)

/-! ### The function on `X` -/

variable {F : Type*} [Field F] [NumberField F]

lemma WX_eq (s : ℂ) (ν : F) (P : X F) :
    WX s ν P = ∏ w : InfinitePlace F, ((P.v w : ℝ) : ℂ) ^ (2 - s) *
      sourceFourierKernel s (-(w.embedding ν) * P.v w) := by
  unfold WX Winf
  exact Finset.prod_congr rfl fun w _ => jacquet_eq_sourceFourierKernel s _ (P.v_pos w)

theorem continuous_WX {s : ℂ} (hs : 1 < s.re) (ν : F) : Continuous (WX s ν : X F → ℂ) := by
  have e : (WX s ν : X F → ℂ) = fun P => ∏ w : InfinitePlace F, ((P.v w : ℝ) : ℂ) ^ (2 - s) *
      sourceFourierKernel s (-(w.embedding ν) * P.v w) := funext fun P => WX_eq s ν P
  rw [e]
  refine continuous_finsetProd _ fun w _ => ?_
  have hv : Continuous fun P : X F => ((P.v w : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (X.continuous_v w)
  refine (hv.cpow continuous_const fun P => Or.inl ?_).mul
    ((continuous_sFK hs).comp (continuous_const.mul hv))
  simpa using P.v_pos w

theorem differentiableOn_WX {ν : F} (hν : ν ≠ 0) (P : X F) :
    DifferentiableOn ℂ (fun s => WX s ν P) {s : ℂ | 1 < s.re} := by
  unfold WX Winf
  have h : ∀ w ∈ (Finset.univ : Finset (InfinitePlace F)), DifferentiableOn ℂ
      (fun s => jacquet s (-(w.embedding ν)) (P.v w)) {s : ℂ | 1 < s.re} := fun w _ =>
    differentiableOn_jacquet _ (by simpa using hν) (P.v_pos w)
  have h2 := DifferentiableOn.finsetProd h
  have e : (∏ w : InfinitePlace F, fun s => jacquet s (-(w.embedding ν)) (P.v w))
      = fun s => ∏ w : InfinitePlace F, jacquet s (-(w.embedding ν)) (P.v w) := by
    funext s; simp [Finset.prod_apply]
  rwa [e] at h2

/-- Uniform bound on `ball × box`. -/
theorem exists_norm_WX_le (ν : F) (n : ℕ) {s₀ : ℂ} (hs₀ : 1 < s₀.re) :
    ∃ R B : ℝ, 0 < R ∧ ball s₀ R ⊆ {s : ℂ | 1 < s.re} ∧
      ∀ s ∈ ball s₀ R, ∀ P ∈ (X.box n : Set (X F)), ‖WX s ν P‖ ≤ B := by
  set R : ℝ := (s₀.re - 1) / 2 with hR
  have hR0 : 0 < R := by rw [hR]; linarith
  have hre : ∀ s ∈ ball s₀ R, s₀.re - R < s.re ∧ |2 - s.re| ≤ 2 + ‖s₀‖ + R := by
    intro s hs
    have h1 : ‖s - s₀‖ < R := mem_ball_iff_norm.mp hs
    have h2 : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
    have h3 : |s₀.re| ≤ ‖s₀‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re] at h2
    have h4 := abs_le.mp (h2.trans h1.le)
    have h5 := abs_le.mp h3
    refine ⟨by linarith [(abs_lt.mp (lt_of_le_of_lt h2 h1)).1], abs_le.mpr ⟨?_, ?_⟩⟩ <;> linarith
  set a : ℝ := (n : ℝ) + 1 with ha
  have ha1 : 1 ≤ a := by rw [ha]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set b : ℝ := a ^ (2 + ‖s₀‖ + R) * (Real.pi / R) with hb
  refine ⟨R, ∏ _w : InfinitePlace F, b, hR0, fun s hs => ?_, fun s hs P hP => ?_⟩
  · have := (hre s hs).1
    change 1 < s.re
    rw [hR] at this; linarith
  · obtain ⟨hs1, hs2⟩ := hre s hs
    have hs' : 1 < s.re := by rw [hR] at hs1; linarith
    rw [WX_eq, norm_prod]
    refine Finset.prod_le_prod (fun w _ => norm_nonneg _) fun w _ => ?_
    have hvP := ((mem_box_iff n P).mp hP).2 w
    have hv0 : 0 < P.v w := P.v_pos w
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv0]
    have e1 : (2 - s).re = 2 - s.re := by simp
    rw [e1, hb]
    refine mul_le_mul (rpow_le_of_mem ha1 hvP.1 hvP.2 hs2) ?_ (norm_nonneg _) (by positivity)
    refine (norm_sFK_le hs' _).trans ?_
    have hRle : R ≤ s.re - 1 := by rw [hR] at hs1 ⊢; linarith
    exact div_le_div_of_nonneg_left Real.pi_pos.le hR0 hRle

/-- **Non-vanishing near the cusp**, for every complex `s₁` with `Re s₁ > 1`. -/
theorem exists_WX_ne_zero (ν : F) {s₁ : ℂ} (hs₁ : 1 < s₁.re) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ P : X F, (∀ w, P.v w < δ) → WX s₁ ν P ≠ 0 := by
  obtain ⟨ε, hε, hne⟩ := exists_sFK_ne_zero hs₁
  set m : ℝ := ∑ w : InfinitePlace F, ‖w.embedding ν‖ with hm
  have hm0 : 0 ≤ m := Finset.sum_nonneg fun w _ => norm_nonneg _
  refine ⟨ε / (m + 1), by positivity, fun P hP => ?_⟩
  rw [WX_eq]
  refine Finset.prod_ne_zero_iff.mpr fun w _ => mul_ne_zero ?_ (hne _ ?_)
  · rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (P.v_pos w).ne')]
    exact Complex.exp_ne_zero _
  · rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (P.v_pos w)]
    have h1 : ‖w.embedding ν‖ ≤ m :=
      Finset.single_le_sum (f := fun w : InfinitePlace F => ‖w.embedding ν‖)
        (fun w _ => norm_nonneg _) (Finset.mem_univ w)
    have h2 : P.v w < ε / (m + 1) := hP w
    calc ‖w.embedding ν‖ * P.v w ≤ m * P.v w :=
          mul_le_mul_of_nonneg_right h1 (P.v_pos w).le
      _ ≤ (m + 1) * P.v w := by nlinarith [P.v_pos w]
      _ < (m + 1) * (ε / (m + 1)) := mul_lt_mul_of_pos_left h2 (by positivity)
      _ = ε := by field_simp

/-! ### The phase test function -/

variable [IsTotallyComplex F]

lemma measurable_unitPhase : Measurable unitPhase :=
  measurable_id.div (Complex.measurable_ofReal.comp measurable_norm)

lemma norm_unitPhase_le (z : ℂ) : ‖unitPhase z‖ ≤ 1 := by
  unfold unitPhase
  rw [norm_div, Complex.norm_real, norm_norm]
  exact div_self_le_one _

lemma conj_unitPhase_mul (z : ℂ) : conj (unitPhase z) * z = ((‖z‖ : ℝ) : ℂ) := by
  unfold unitPhase
  by_cases hz : z = 0
  · simp [hz]
  have h0 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  rw [map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, Complex.conj_mul']
  field_simp

lemma measurable_phaseW {s₁ : ℂ} (hs₁ : 1 < s₁.re) (ν : F) :
    Measurable (phaseW (F := F) s₁ ν) :=
  measurable_unitPhase.comp ((continuous_WX hs₁ ν).measurable.comp
    (measurable_ofXV.comp (measurable_const.prodMk measurable_id)))

lemma norm_phaseW_le (s₁ : ℂ) (ν : F) (v : InfinitePlace F → ℝ) : ‖phaseW s₁ ν v‖ ≤ 1 :=
  norm_unitPhase_le _

lemma phaseW_v (s₁ : ℂ) (ν : F) (P : X F) : phaseW s₁ ν P.v = unitPhase (WX s₁ ν P) := by
  unfold phaseW
  have h : (ofXV ((0 : InfinitePlace F → ℂ), P.v)).v = P.v := by
    rw [ofXV_eq_mk 0 (fun w => P.v_pos w)]
    rfl
  unfold WX
  rw [h]

lemma conj_phaseW_mul (s₁ : ℂ) (ν : F) (P : X F) :
    conj (phaseW s₁ ν P.v) * WX s₁ ν P = ((‖WX s₁ ν P‖ : ℝ) : ℂ) := by
  rw [phaseW_v, conj_unitPhase_mul]

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Lat
/-! # WP-T, file 3: the lattices `Λ_Γ` (translations of `Γ`) and `Λ_M` (`B.transLat 𝔪 M`)

Both sit in `latO F = emb(𝓞_F)` (for `M ≥ 0`) and contain the image of a nonzero ideal, hence are
commensurable: `relIndex_inf_left/right`.

* `pcell_of_hfund`: WP-X2/WP-RF's `hfund` is a strict cell `T.PCell (N.latN Γ) D`;
  `exists_pcell_latN`.
* `exists_pcell_transLat`: a bounded strict cell of `Λ_M` (`M ≥ 0`), as a union of translates of a
  cell of `emb(𝓞_F)`;  `cellM 𝔪 M` (a chosen one, bounded by `cellN 𝔪 M`).
* `kap 𝔪 M = (vol(cellM 𝔪 M) · vol(𝔩_M))⁻¹` — the constant of all coefficient formulas
  (`= covol(𝓞_F)⁻¹` by WP-B's stub B-2; independent of the chosen cell: `volume_eq_cellM`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}

/-! ### Ideal lattices -/

/-! ### The two families of lattices -/

/-! ### Cells -/

lemma volume_ne_top_of_bdd {D : Set (InfinitePlace F → ℂ)} {n : ℕ}
    (h : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) : volume D ≠ ⊤ := by
  have hsub : D ⊆ Metric.closedBall (0 : InfinitePlace F → ℂ) n := fun x hx => by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)]
    exact h x hx
  exact ((measure_mono hsub).trans_lt measure_closedBall_lt_top).ne

lemma integrableOn_of_bdd {D : Set (InfinitePlace F → ℂ)} {n : ℕ}
    (h : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) {f : (InfinitePlace F → ℂ) → ℂ} (hf : Continuous f) :
    IntegrableOn f D volume := by
  have hsub : D ⊆ Metric.closedBall (0 : InfinitePlace F → ℂ) n := fun x hx => by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)]
    exact h x hx
  exact (hf.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set hsub

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Coef
/-! # WP-T, file 4: the `ν`-th coefficient of `E_Φ` over a cell, for `Re s > 2`

* `freq ν = (−2σ_w ν)_w`: `conj (RF.eChar (freq ν) x) = B.chiInf ν x`, so that
  `X.coeffFunctional Γ n (RF.stripFn D (freq ν) φ) …` is the `ν`-th coefficient against `conj φ`.
* `HasCoefT Ψ ν' a₀ D κ` (twisted section, any coefficient series `a₀`): for `Re s > 2` and all
  `v`, `∫_D E_Ψ(x, v) conj e_∞(ν'x) dx = vol(D)·κ·W_s(ν'; v)·a₀(s)`;
  `HasCoef hG hz6 Φ ν D κ` is the case `Ψ = Φ.twist`, `a₀ = 𝔞_Φ(ν, ·)`.
  - `hasCoef_transLat`: a strict cell of `Λ_M` (`M ≥ 0` valid) has it with `κ = kap 𝔪 M` (WP-B);
  - **`hasCoef_latN`**: so has every bounded strict cell of the translation lattice of any `Γ`
    fixing `Φ.twist`, provided `conj e_∞(ν·)` is `Λ_Γ`-periodic (`T.mean_eq`).
* `Afun Γ Ψ n ψ s = ∫_{box n} conj ψ · lift (resPart Γ Ψ s) + ∫_{box n} conj ψ · h_s`: holomorphic
  on `E.slit`, `= ∫_{box n} conj ψ · E_Ψ` for `Re s > 2`, ray limit `∫ conj ψ · θ`.
* `Wc D n φ ν s = N.cf D n φ (WX s ν)`: holomorphic on `Re s > 1`; `exists_Wc_ne_zero`.
* **`Afun_eq_of_hasCoefT`**: `Afun … (stripFn D (freq ν') φ) s = κ·a₀(s)·Wc D n φ ν' s`, `Re s > 2`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### The frequency of `ν` in WP-RF's parametrization -/

theorem conj_eChar_freq (ν : F) (x : InfinitePlace F → ℂ) :
    conj (eChar (freq ν) x) = chiInf ν x := by
  have h1 : chiInf ν x = Complex.exp (2 * Real.pi * Complex.I *
      ((∑ w : InfinitePlace F, 2 * (w.embedding ν * x w).re : ℝ) : ℂ)) := by
    rw [chiInf_eq_prod]
    simp only [archChar_eq_re, neg_neg]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum]
  have h2 : pair (freq ν) x = -∑ w : InfinitePlace F, 2 * (w.embedding ν * x w).re := by
    unfold pair freq
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    have e : -2 * w.embedding ν * x w = ((-2 : ℝ) : ℂ) * (w.embedding ν * x w) := by
      push_cast; ring
    rw [e, Complex.re_ofReal_mul]
    ring
  rw [h1, eChar, h2, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

lemma conj_stripFn (D : Set (InfinitePlace F → ℂ)) (ν : F) (φ : (InfinitePlace F → ℝ) → ℂ)
    (Q : X F) :
    conj (stripFn D (freq ν) φ Q) = conj (stripFn D 0 φ Q) * chiInf ν Q.x := by
  rw [stripFn_zero, stripFn, map_mul, map_mul, map_mul, conj_eChar_freq]
  ring

lemma continuous_x_pi : Continuous (X.x : X F → InfinitePlace F → ℂ) :=
  continuous_pi fun w => X.continuous_x w

/-! ### Cells that compute the coefficient -/

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)
  (ν : SInt 𝔪)

variable {hG hz6 Φ ν}

/-! ### The coefficient function of the continuation -/

section Afun

variable (hG) {Γ : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex] {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ)
  (n : ℕ) {ψ : X F → ℂ} (hψ : Measurable ψ) {C : ℝ} (hC : ∀ Q, ‖ψ Q‖ ≤ C)

lemma Afun_eq_functional (s : ℂ) :
    Afun Γ Ψ n ψ s = X.coeffFunctional Γ n ψ hψ C hC (resPart Γ Ψ s) + hInt Ψ n ψ s := by
  rw [Afun, X.coeffFunctional_apply]

include hG hΓ hψ hC in
theorem Afun_eq_eis {s : ℂ} (hs : 2 < s.re) :
    Afun Γ Ψ n ψ s = ∫ Q in X.box n, conj (ψ Q) * eis Ψ s Q ∂X.vol F := by
  rw [Afun_eq_functional n hψ hC]
  exact coeff_resPart_add_hInt hG Γ hΓ hs (GL.eisEigen_of_two_lt_re hG.ne_bot Ψ hs) n ψ hψ C hC

end Afun

/-! ### The archimedean factor -/

theorem differentiableOn_Wc {ν : F} (hν : ν ≠ 0) {D : Set (InfinitePlace F → ℂ)}
    (hD : MeasurableSet D) (n : ℕ) {φ : (InfinitePlace F → ℝ) → ℂ} (hφ : Measurable φ)
    (hφ1 : ∀ v, ‖φ v‖ ≤ 1) : DifferentiableOn ℂ (Wc D n φ ν) {s : ℂ | 1 < s.re} := by
  intro s₀ hs₀
  refine DifferentiableAt.differentiableWithinAt ?_
  obtain ⟨R, B, hR, hsub, hB⟩ := exists_norm_WX_le (F := F) ν n hs₀
  refine differentiableAt_setIntegral (X.measurableSet_box n) (X.vol_box_lt_top n).ne
    (R := R) (B₀ := B) hR
    (fun s hs => (Complex.continuous_conj.measurable.comp (measurable_stripFn hD 0 hφ)).mul
      (continuous_WX (hsub hs) ν).measurable)
    (fun Q _ => (((differentiableOn_WX hν Q).mono hsub).const_mul _))
    (fun s hs Q hQ => ?_)
  rw [norm_mul, RCLike.norm_conj]
  calc ‖stripFn D 0 φ Q‖ * ‖WX s ν Q‖ ≤ 1 * ‖WX s ν Q‖ :=
        mul_le_mul_of_nonneg_right (norm_stripFn_le D 0 hφ1 Q) (norm_nonneg _)
    _ ≤ B := by rw [one_mul]; exact hB s hs Q hQ

lemma isOpen_re_gt_one : IsOpen {s : ℂ | 1 < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

/-- `nuV` of a small box near `v = 0` is positive. -/
lemma nuV_Icc_ne_zero {n : ℕ} {lo hi : ℝ} (hlo : 1 / ((n : ℝ) + 1) ≤ lo) (hlh : lo < hi)
    (hhi : hi ≤ (n : ℝ) + 1) :
    X.nuV F (Icc (fun _ : InfinitePlace F => lo) (fun _ : InfinitePlace F => hi)) ≠ 0 := by
  have hsub : Icc (fun _ : InfinitePlace F => lo) (fun _ : InfinitePlace F => hi) ⊆ vBox F n := by
    intro v hv w
    exact ⟨hlo.trans (hv.1 w), (hv.2 w).trans hhi⟩
  rw [nuV_eq_withDensity, withDensity_apply _ measurableSet_Icc]
  intro h
  rw [lintegral_eq_zero_iff RF.measurable_dens] at h
  have h1 : ∀ᵐ v ∂(volume : Measure (InfinitePlace F → ℝ)),
      v ∉ Icc (fun _ : InfinitePlace F => lo) (fun _ : InfinitePlace F => hi) := by
    have h2 := (ae_restrict_iff' measurableSet_Icc).mp h
    filter_upwards [h2] with v hv hmem
    exact dens_ne_zero (hsub hmem) (hv hmem)
  have h3 := measure_eq_zero_iff_ae_notMem.mpr h1
  rw [Real.volume_Icc_pi] at h3
  exact (Finset.prod_ne_zero_iff.mpr fun w _ =>
    (ENNReal.ofReal_pos.mpr (by linarith)).ne') h3

/-- **A test function seeing `W_{s₁}(ν; ·)`**, for every complex `s₁` with `Re s₁ > 1`. -/
theorem exists_Wc_ne_zero (ν : F) {s₁ : ℂ} (hs₁ : 1 < s₁.re) {D : Set (InfinitePlace F → ℂ)}
    (hDm : MeasurableSet D) (hD0 : volume D ≠ 0) {n₀ : ℕ} (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n₀) :
    ∃ n : ℕ, n₀ ≤ n ∧ Wc D n (phaseW s₁ ν) ν s₁ ≠ 0 := by
  obtain ⟨δ, hδ, hne⟩ := exists_WX_ne_zero (F := F) ν hs₁
  set δ' : ℝ := min δ 1 with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ one_pos
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / δ')
  set n : ℕ := max n₀ m with hn
  have hnm : (m : ℝ) ≤ n := by exact_mod_cast le_max_right n₀ m
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set lo : ℝ := 1 / ((n : ℝ) + 1) with hlo
  have hlo_lt : lo < δ' := by
    rw [hlo, one_div_lt (by positivity) hδ'0]
    linarith
  set hi : ℝ := (lo + δ') / 2 with hhi
  have hlh : lo < hi := by rw [hhi]; linarith
  have hhiδ : hi < δ := by
    have : δ' ≤ δ := min_le_left _ _
    rw [hhi]; linarith
  have hhin : hi ≤ (n : ℝ) + 1 := by
    have : δ' ≤ 1 := min_le_right _ _
    rw [hhi]; linarith
  refine ⟨n, le_max_left _ _, ?_⟩
  set V' : Set (InfinitePlace F → ℝ) :=
    Icc (fun _ : InfinitePlace F => lo) (fun _ : InfinitePlace F => hi) with hV'
  have hV'sub : V' ⊆ vBox F n := fun v hv w => ⟨hv.1 w, (hv.2 w).trans hhin⟩
  have hbn : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n := fun x hx w =>
    (hb x hx w).trans (by exact_mod_cast le_max_left n₀ m)
  set h : X F → ℝ := (X.x ⁻¹' D : Set (X F)).indicator (fun Q => ‖WX s₁ ν Q‖) with hh
  have hSm : MeasurableSet (X.x ⁻¹' D : Set (X F)) := X.measurable_x hDm
  have e : ∀ Q : X F, conj (stripFn D 0 (phaseW s₁ ν) Q) * WX s₁ ν Q = ((h Q : ℝ) : ℂ) := by
    intro Q
    rw [stripFn_zero, hh]
    by_cases hQ : Q.x ∈ D
    · rw [indicator_of_mem hQ, indicator_of_mem (show Q ∈ X.x ⁻¹' D from hQ), one_mul,
        conj_phaseW_mul]
    · rw [indicator_of_notMem hQ, indicator_of_notMem (show Q ∉ X.x ⁻¹' D from hQ)]
      simp
  have hWint : IntegrableOn (WX s₁ ν : X F → ℂ) (X.box n) (X.vol F) :=
    (continuous_WX hs₁ ν).continuousOn.integrableOn_compact (isCompact_box n)
  have hint0 := cf_integrable (n := n) hDm (measurable_phaseW hs₁ ν) (norm_phaseW_le s₁ ν) hWint
  have hint : IntegrableOn h (X.box n) (X.vol F) := by
    have := hint0.norm
    refine this.congr (Eventually.of_forall fun Q => ?_)
    change ‖conj (stripFn D 0 (phaseW s₁ ν) Q) * WX s₁ ν Q‖ = h Q
    rw [e Q, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    rw [hh]
    exact indicator_nonneg (fun Q _ => norm_nonneg _) Q
  have hnonneg : 0 ≤ᵐ[(X.vol F).restrict (X.box n)] h :=
    Eventually.of_forall fun Q => indicator_nonneg (fun Q _ => norm_nonneg _) Q
  have hWc : Wc D n (phaseW s₁ ν) ν s₁ = ((∫ Q in X.box n, h Q ∂X.vol F : ℝ) : ℂ) := by
    unfold Wc cf
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall e)
  rw [hWc]
  refine Complex.ofReal_ne_zero.mpr (ne_of_gt ?_)
  rw [integral_pos_iff_support_of_nonneg_ae hnonneg hint]
  -- the support contains `{x ∈ D, v ∈ V'}`, of positive measure
  set S' : Set (X F) := X.v ⁻¹' V' ∩ X.x ⁻¹' D with hS'
  have hVm : MeasurableSet (X.v ⁻¹' V' : Set (X F)) := X.measurable_v measurableSet_Icc
  have hS'sub : S' ⊆ Function.support h ∩ X.box n := by
    rintro Q ⟨hQv, hQx⟩
    refine ⟨?_, (mem_box_iff n Q).mpr ⟨hbn _ hQx, hV'sub hQv⟩⟩
    rw [Function.mem_support, hh, indicator_of_mem hQx]
    exact norm_ne_zero_iff.mpr (hne Q fun w => lt_of_le_of_lt (hQv.2 w) hhiδ)
  have hS'pos : X.vol F S' ≠ 0 := by
    have h1 := X.setLIntegral_strip (F := F) hDm
      (f := fun p => V'.indicator (fun _ => (1 : ℝ≥0∞)) p.2)
      ((measurable_const.indicator measurableSet_Icc).comp measurable_snd)
    have h2 : ∫⁻ Q in (X.x ⁻¹' D : Set (X F)), V'.indicator (fun _ => (1 : ℝ≥0∞)) Q.v
        ∂X.vol F = X.vol F S' := by
      have e' : (fun Q : X F => V'.indicator (fun _ => (1 : ℝ≥0∞)) Q.v)
          = (X.v ⁻¹' V' : Set (X F)).indicator 1 := by
        funext Q
        by_cases hQ : Q.v ∈ V'
        · rw [indicator_of_mem hQ, indicator_of_mem (show Q ∈ X.v ⁻¹' V' from hQ)]; rfl
        · rw [indicator_of_notMem hQ, indicator_of_notMem (show Q ∉ X.v ⁻¹' V' from hQ)]
      rw [e', lintegral_indicator_one hVm, Measure.restrict_apply hVm]
    rw [← h2, h1]
    have h3 : ∀ x : InfinitePlace F → ℂ,
        ∫⁻ v, (fun p : (InfinitePlace F → ℂ) × (InfinitePlace F → ℝ) =>
          V'.indicator (fun _ => (1 : ℝ≥0∞)) p.2) (x, v) ∂X.nuV F = X.nuV F V' := fun _ =>
      lintegral_indicator_one measurableSet_Icc
    rw [lintegral_congr h3, lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact mul_ne_zero (nuV_Icc_ne_zero (le_of_eq hlo.symm) hlh hhin) hD0
  rw [Measure.restrict_apply' (X.measurableSet_box n)]
  exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hS'pos) (measure_mono hS'sub)

/-! ### The coefficient of the series over an admissible cell -/

section main

variable {Ψ : TSection ι 𝔪} {ν' : F} {a₀ : ℂ → ℂ} {D : Set (InfinitePlace F → ℂ)} {κ : ℂ}
  {n : ℕ} {φ : (InfinitePlace F → ℝ) → ℂ}

/-- For `Re s > 2`: `∫_{box n} conj (stripFn D (freq ν') φ) · E_Ψ = κ·a₀(s)·Wc D n φ ν' s`. -/
theorem integral_eis_of_hasCoefT (h𝔪 : 𝔪 ≠ ⊥) (h : HasCoefT Ψ ν' a₀ D κ) (hDm : MeasurableSet D)
    (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1) {s : ℂ}
    (hs : 2 < s.re) :
    ∫ Q in X.box n, conj (stripFn D (freq ν') φ Q) * eis Ψ s Q ∂X.vol F
      = κ * a₀ s * Wc D n φ ν' s := by
  have hs1 : 1 < s.re := by linarith
  set c : ℂ := κ * a₀ s with hc
  have hchi : Continuous fun Q : X F => chiInf ν' Q.x :=
    (continuous_chiInf _).comp continuous_x_pi
  have hEc : Continuous fun Q : X F => chiInf ν' Q.x * eis Ψ s Q :=
    hchi.mul (continuous_eis h𝔪 Ψ hs)
  have hint1 : IntegrableOn (fun Q : X F => chiInf ν' Q.x * eis Ψ s Q) (X.box n)
      (X.vol F) := hEc.continuousOn.integrableOn_compact (isCompact_box n)
  have hint2 : IntegrableOn (fun Q : X F => c * WX s ν' Q) (X.box n) (X.vol F) :=
    ((continuous_WX hs1 ν').const_mul c).continuousOn.integrableOn_compact
      (isCompact_box n)
  have hzero : cf D n φ (fun Q => chiInf ν' Q.x * eis Ψ s Q - c * WX s ν' Q) = 0 := by
    refine cf_eq_zero_of_fibers hDm hb hφ hφ1
      (hEc.measurable.sub ((continuous_WX hs1 ν').const_mul c).measurable)
      (hint1.sub hint2) fun v hv => ?_
    have hfc : Continuous fun x : InfinitePlace F → ℂ =>
        chiInf ν' x * eis Ψ s (X.mk x v hv) :=
      (continuous_chiInf _).mul ((continuous_eis h𝔪 Ψ hs).comp (continuous_mk_x v hv))
    have e : ∀ x : InfinitePlace F → ℂ,
        chiInf ν' (X.mk x v hv).x * eis Ψ s (X.mk x v hv) - c * WX s ν' (X.mk x v hv)
          = chiInf ν' x * eis Ψ s (X.mk x v hv) - c * Winf s ν' v := fun x => rfl
    simp only [e]
    rw [integral_sub (integrableOn_of_bdd hb hfc)
      (integrableOn_const (volume_ne_top_of_bdd hb)), setIntegral_const, Complex.real_smul,
      measureReal_def]
    have h1 := h s hs v hv
    simp only [mul_comm (eis _ _ _) _] at h1
    rw [h1, hc]
    ring
  rw [cf_sub hDm hφ hφ1 hint1 ((continuous_WX hs1 ν').continuousOn.integrableOn_compact
    (isCompact_box n) |>.const_mul c), cf_const_mul] at hzero
  have e2 : cf D n φ (fun Q => chiInf ν' Q.x * eis Ψ s Q)
      = ∫ Q in X.box n, conj (stripFn D (freq ν') φ Q) * eis Ψ s Q ∂X.vol F := by
    unfold cf
    refine integral_congr_ae (Eventually.of_forall fun Q => ?_)
    change _ = conj (stripFn D (freq ν') φ Q) * eis Ψ s Q
    rw [conj_stripFn]
    ring
  rw [← e2, sub_eq_zero.mp hzero]
  rfl

/-- **The coefficient of the continuation, on `Re s > 2`.** -/
theorem Afun_eq_of_hasCoefT (hG : Good 𝔪) (h : HasCoefT Ψ ν' a₀ D κ) (hDm : MeasurableSet D)
    (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1)
    {Γ : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex] (hΓ : Inv Γ Ψ) {s : ℂ}
    (hs : 2 < s.re) :
    Afun Γ Ψ n (stripFn D (freq ν') φ) s = κ * a₀ s * Wc D n φ ν' s := by
  rw [Afun_eq_eis hG hΓ n (measurable_stripFn hDm _ hφ) (norm_stripFn_le D _ hφ1) hs]
  exact integral_eis_of_hasCoefT hG.ne_bot h hDm hb hφ hφ1 hs

end main

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Cont
/-! # WP-T, file 5: the continuation of the coefficient series and its residue (generic form)

Function level (`E.slit`, the ray `N.ray t = 4/3 + t(1+i)`):
* `contSlit a₀` — the holomorphic function on `E.slit` agreeing with `a₀` on `Re s > 2`, if there
  is one (`contSlit_spec`, `contSlit_unique`);
* `resSlit a₀ = lim_{t↓0} (s_t − 4/3)·contSlit a₀ (s_t)`.

For a twisted section `Ψ`, a frequency `ν' ≠ 0` and a coefficient series `a₀` with one admissible
cell (`HasSeed Ψ ν' a₀`: some bounded measurable `D₀` of positive volume with
`HasCoefT Ψ ν' a₀ D₀ κ₀`, `κ₀ ≠ 0`):
* `differentiableOn_contSlit`, `contSlit_eq` — MATH2 (C6) for `ν' ≠ 0`;
* **`Afun_eq_contSlit`**: for every `Γ` fixing `Ψ`, every admissible cell `(D, κ)`, every box
  `n ⊇ D` and test function `φ`, on all of `E.slit`
  `∫_{box n} conj (stripFn D (freq ν') φ) · E^{ext} = κ · contSlit a₀ s · Wc D n φ ν' s`;
* `tendsto_resSlit` — MATH2 (C7); `hasResOn` (the `E.HasResOn` statement);
* **`integral_theta_of_hasCoefT`**:
  `∫_{box n} conj (stripFn D (freq ν') φ) · θ_Ψ = κ · resSlit a₀ · Wc D n φ ν' (4/3)`.

The genuine sections `Φ` (`Ψ = Φ.twist`, `a₀ = 𝔞_Φ(ν, ·)`) are in `T_Theta`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

lemma eqOn_slit {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f E.slit)
    (hg : DifferentiableOn ℂ g E.slit) (h : ∀ s : ℂ, 2 < s.re → f s = g s) :
    EqOn f g E.slit := by
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ) (z₀ := (3 : ℂ))
    (hf.analyticOnNhd isOpen_slit) (hg.analyticOnNhd isOpen_slit)
    E.isPreconnected_slit ⟨by norm_num, fun _ => by norm_num⟩ ?_
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show (2 : ℝ) < (3 : ℂ).re by norm_num)] with s hs
  exact h s hs

lemma slit_subset_re : E.slit ⊆ {s : ℂ | 1 < s.re} := fun _ hs => hs.1

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ}

/-! ### Function level -/

theorem contSlit_spec {a₀ : ℂ → ℂ}
    (h : ∃ a : ℂ → ℂ, DifferentiableOn ℂ a E.slit ∧ ∀ s : ℂ, 2 < s.re → a s = a₀ s) :
    DifferentiableOn ℂ (contSlit a₀) E.slit ∧ ∀ s : ℂ, 2 < s.re → contSlit a₀ s = a₀ s := by
  unfold contSlit; rw [dif_pos h]
  exact h.choose_spec

/-- Uniqueness: any holomorphic function on `E.slit` agreeing with `a₀` is `contSlit a₀`. -/
theorem contSlit_unique {a₀ a : ℂ → ℂ} (ha : DifferentiableOn ℂ a E.slit)
    (h : ∀ s : ℂ, 2 < s.re → a s = a₀ s) : EqOn a (contSlit a₀) E.slit := by
  have hs := contSlit_spec ⟨a, ha, h⟩
  exact eqOn_slit ha hs.1 fun s hs' => (h s hs').trans (hs.2 s hs').symm

theorem resSlit_eq {a₀ : ℂ → ℂ} {τ : ℂ}
    (h : Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * contSlit a₀ (ray t)) (𝓝[>] 0)
      (𝓝 τ)) : resSlit a₀ = τ :=
  h.limUnder_eq

/-! ### Twisted sections with a coefficient series -/

variable (Pk : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  {Ψ : TSection ι 𝔪} {ν' : F} {a₀ : ℂ → ℂ}

include Pk hG hz6 in
/-- **MATH2 (C6), `ν' ≠ 0`.**  Existence of the continuation with its characterizing property. -/
theorem exists_cont (hν' : ν' ≠ 0) (hseed : HasSeed Ψ ν' a₀) :
    ∃ a : ℂ → ℂ, DifferentiableOn ℂ a E.slit ∧ (∀ s : ℂ, 2 < s.re → a s = a₀ s) ∧
    ∀ (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex], Inv Γ Ψ →
      ∀ (D : Set (InfinitePlace F → ℂ)) (κ : ℂ) (n : ℕ) (φ : (InfinitePlace F → ℝ) → ℂ),
        HasCoefT Ψ ν' a₀ D κ → MeasurableSet D → (∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) → Measurable φ →
        (∀ v, ‖φ v‖ ≤ 1) → ∀ s ∈ E.slit,
          Afun Γ Ψ n (stripFn D (freq ν') φ) s = κ * a s * Wc D n φ ν' s := by
  obtain ⟨Γ₀, hfi, hΓ₀⟩ := exists_finiteIndex_inv Pk hG hz6 Ψ
  obtain ⟨D₀, κ₀, n₀, hcoef, hk, hD₀m, hvol0, hb₀⟩ := hseed
  choose! nAt hnAt using fun (s₁ : ℂ) (hs₁ : 1 < s₁.re) =>
    exists_Wc_ne_zero ν' hs₁ hD₀m hvol0 hb₀
  set A : ℕ → ((InfinitePlace F → ℝ) → ℂ) → ℂ → ℂ := fun n φ s =>
    Afun Γ₀ Ψ n (stripFn D₀ (freq ν') φ) s with hA
  set W : ℕ → ((InfinitePlace F → ℝ) → ℂ) → ℂ → ℂ := fun n φ s => Wc D₀ n φ ν' s with hW
  have hbn : ∀ n : ℕ, n₀ ≤ n → ∀ x ∈ D₀, ∀ w, ‖x w‖ ≤ n := fun n hn x hx w =>
    (hb₀ x hx w).trans (by exact_mod_cast hn)
  have hAd : ∀ (n : ℕ) (φ : (InfinitePlace F → ℝ) → ℂ), Measurable φ → (∀ v, ‖φ v‖ ≤ 1) →
      DifferentiableOn ℂ (A n φ) E.slit := fun n φ hφ hφ1 =>
    differentiableOn_Afun hG hΓ₀ n (measurable_stripFn hD₀m _ hφ) (norm_stripFn_le _ _ hφ1)
  have hAe : ∀ (n : ℕ) (φ : (InfinitePlace F → ℝ) → ℂ), n₀ ≤ n → Measurable φ →
      (∀ v, ‖φ v‖ ≤ 1) → ∀ s : ℂ, 2 < s.re → A n φ s = κ₀ * a₀ s * W n φ s :=
    fun n φ hn hφ hφ1 s hs => Afun_eq_of_hasCoefT hG hcoef hD₀m (hbn n hn) hφ hφ1 hΓ₀ hs
  have hWd : ∀ (n : ℕ) (φ : (InfinitePlace F → ℝ) → ℂ), Measurable φ → (∀ v, ‖φ v‖ ≤ 1) →
      DifferentiableOn ℂ (W n φ) E.slit := fun n φ hφ hφ1 =>
    (differentiableOn_Wc hν' hD₀m n hφ hφ1).mono slit_subset_re
  have hcross : ∀ (n : ℕ) (φ : (InfinitePlace F → ℝ) → ℂ) (n' : ℕ)
      (φ' : (InfinitePlace F → ℝ) → ℂ), n₀ ≤ n → Measurable φ → (∀ v, ‖φ v‖ ≤ 1) →
      n₀ ≤ n' → Measurable φ' → (∀ v, ‖φ' v‖ ≤ 1) → ∀ s ∈ E.slit,
      A n φ s * W n' φ' s = A n' φ' s * W n φ s := by
    intro n φ n' φ' hn hφ hφ1 hn' hφ' hφ1'
    refine eqOn_slit ((hAd n φ hφ hφ1).mul (hWd n' φ' hφ' hφ1'))
      ((hAd n' φ' hφ' hφ1').mul (hWd n φ hφ hφ1)) fun s hs => ?_
    rw [hAe n φ hn hφ hφ1 s hs, hAe n' φ' hn' hφ' hφ1' s hs]
    ring
  set a : ℂ → ℂ := fun s =>
    A (nAt s) (phaseW s ν') s / (κ₀ * W (nAt s) (phaseW s ν') s) with ha
  have hkey : ∀ (n : ℕ) (φ : (InfinitePlace F → ℝ) → ℂ), n₀ ≤ n → Measurable φ →
      (∀ v, ‖φ v‖ ≤ 1) → ∀ s ∈ E.slit, A n φ s = κ₀ * a s * W n φ s := by
    intro n φ hn hφ hφ1 s hs
    have hs1 : 1 < s.re := hs.1
    obtain ⟨hn1, hW0⟩ := hnAt s hs1
    have hc := hcross n φ (nAt s) (phaseW s ν') hn hφ hφ1 hn1 (measurable_phaseW hs1 _)
      (norm_phaseW_le s _) s hs
    have h1 : A n φ s = A (nAt s) (phaseW s ν') s * W n φ s / W (nAt s) (phaseW s ν') s := by
      rw [eq_div_iff hW0]; exact hc
    rw [h1, ha]
    field_simp
  have ha_eq : ∀ s : ℂ, 2 < s.re → a s = a₀ s := by
    intro s hs
    have hs1 : 1 < s.re := by linarith
    obtain ⟨hn1, hW0⟩ := hnAt s hs1
    simp only [ha]
    rw [hAe _ _ hn1 (measurable_phaseW hs1 _) (norm_phaseW_le s _) s hs]
    have hW0' : W (nAt s) (phaseW s ν') s ≠ 0 := hW0
    field_simp
  have ha_diff : DifferentiableOn ℂ a E.slit := by
    intro s₁ hs₁
    refine DifferentiableAt.differentiableWithinAt ?_
    have hs1 : 1 < s₁.re := hs₁.1
    obtain ⟨hn1, hW0⟩ := hnAt s₁ hs1
    have hφm := measurable_phaseW hs1 ν'
    have hφb := norm_phaseW_le s₁ ν'
    have hWdiff : DifferentiableAt ℂ (W (nAt s₁) (phaseW s₁ ν')) s₁ :=
      (differentiableOn_Wc hν' hD₀m (nAt s₁) hφm hφb s₁ hs1).differentiableAt
        (isOpen_re_gt_one.mem_nhds hs1)
    have hne : ∀ᶠ s in 𝓝 s₁, W (nAt s₁) (phaseW s₁ ν') s ≠ 0 :=
      hWdiff.continuousAt.eventually_ne hW0
    have heq : a =ᶠ[𝓝 s₁] fun s => A (nAt s₁) (phaseW s₁ ν') s
        / (κ₀ * W (nAt s₁) (phaseW s₁ ν') s) := by
      filter_upwards [hne, isOpen_slit.mem_nhds hs₁] with s hs hslit
      rw [eq_div_iff (mul_ne_zero hk hs), hkey _ _ hn1 hφm hφb s hslit]
      ring
    have hAdiff := (hAd (nAt s₁) (phaseW s₁ ν') hφm hφb s₁ hs₁).differentiableAt
      (isOpen_slit.mem_nhds hs₁)
    exact (hAdiff.div ((differentiableAt_const _).mul hWdiff)
      (mul_ne_zero hk hW0)).congr_of_eventuallyEq heq
  refine ⟨a, ha_diff, ha_eq, ?_⟩
  intro Γ _ hΓ D κ n φ hc hDm hb hφ hφ1
  refine eqOn_slit (differentiableOn_Afun hG hΓ n (measurable_stripFn hDm _ hφ)
    (norm_stripFn_le D _ hφ1))
    (((differentiableOn_const κ).mul ha_diff).mul
      ((differentiableOn_Wc hν' hDm n hφ hφ1).mono slit_subset_re)) fun s hs => ?_
  rw [Afun_eq_of_hasCoefT hG hc hDm hb hφ hφ1 hΓ hs, ha_eq s hs]

include Pk hG hz6 in
theorem differentiableOn_contSlit (hν' : ν' ≠ 0) (hseed : HasSeed Ψ ν' a₀) :
    DifferentiableOn ℂ (contSlit a₀) E.slit := by
  obtain ⟨a, ha, he, -⟩ := exists_cont Pk hG hz6 hν' hseed
  exact (contSlit_spec ⟨a, ha, he⟩).1

include Pk hG hz6 in
theorem contSlit_eq (hν' : ν' ≠ 0) (hseed : HasSeed Ψ ν' a₀) {s : ℂ} (hs : 2 < s.re) :
    contSlit a₀ s = a₀ s := by
  obtain ⟨a, ha, he, -⟩ := exists_cont Pk hG hz6 hν' hseed
  exact (contSlit_spec ⟨a, ha, he⟩).2 s hs

include Pk hG hz6 in
/-- **The Fourier coefficient of the continued Eisenstein series**, on all of `E.slit`. -/
theorem Afun_eq_contSlit (hν' : ν' ≠ 0) (hseed : HasSeed Ψ ν' a₀)
    {Γ : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex] (hΓ : Inv Γ Ψ)
    {D : Set (InfinitePlace F → ℂ)} {κ : ℂ} {n : ℕ}
    {φ : (InfinitePlace F → ℝ) → ℂ} (hc : HasCoefT Ψ ν' a₀ D κ) (hDm : MeasurableSet D)
    (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1) {s : ℂ}
    (hs : s ∈ E.slit) :
    Afun Γ Ψ n (stripFn D (freq ν') φ) s = κ * contSlit a₀ s * Wc D n φ ν' s := by
  obtain ⟨a, ha, he, hp⟩ := exists_cont Pk hG hz6 hν' hseed
  rw [hp Γ hΓ D κ n φ hc hDm hb hφ hφ1 s hs, contSlit_unique ha he hs]

/-! ### The residue -/

include Pk hG hz6 in
/-- **MATH2 (C7).**  The limit exists, and it gives every Fourier coefficient of `θ`. -/
theorem exists_res (hν' : ν' ≠ 0) (hseed : HasSeed Ψ ν' a₀) : ∃ τ : ℂ,
    Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * contSlit a₀ (ray t)) (𝓝[>] 0) (𝓝 τ) ∧
    ∀ (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex], Inv Γ Ψ →
      ∀ (D : Set (InfinitePlace F → ℂ)) (κ : ℂ) (n : ℕ) (φ : (InfinitePlace F → ℝ) → ℂ),
        HasCoefT Ψ ν' a₀ D κ → MeasurableSet D → (∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) → Measurable φ →
        (∀ v, ‖φ v‖ ≤ 1) →
          ∫ Q in X.box n, conj (stripFn D (freq ν') φ Q) * X.lift Γ (C5.theta Γ Ψ) Q ∂X.vol F
            = κ * τ * Wc D n φ ν' (4 / 3) := by
  have h43 : (1 : ℝ) < ((4 / 3 : ℂ)).re := by norm_num
  -- continuity of `Wc` along the ray
  have hWray : ∀ (D : Set (InfinitePlace F → ℂ)) (n : ℕ) (φ : (InfinitePlace F → ℝ) → ℂ),
      MeasurableSet D → Measurable φ → (∀ v, ‖φ v‖ ≤ 1) →
      Tendsto (fun t : ℝ => Wc D n φ ν' (ray t)) (𝓝[>] 0) (𝓝 (Wc D n φ ν' (4 / 3))) :=
    fun D n φ hDm hφ hφ1 =>
    (((differentiableOn_Wc hν' hDm n hφ hφ1 _ h43).differentiableAt
      (isOpen_re_gt_one.mem_nhds h43)).continuousAt.tendsto).comp tendsto_ray
  obtain ⟨Γ₀, hfi, hΓ₀⟩ := exists_finiteIndex_inv Pk hG hz6 Ψ
  have hseed' := hseed
  obtain ⟨D₀, κ₀, n₀, hcoef, hk, hD₀m, hvol0, hb₀⟩ := hseed'
  obtain ⟨n₁, hn₁, hW0⟩ := exists_Wc_ne_zero ν' h43 hD₀m hvol0 hb₀
  have hbn : ∀ x ∈ D₀, ∀ w, ‖x w‖ ≤ n₁ := fun x hx w =>
    (hb₀ x hx w).trans (by exact_mod_cast hn₁)
  have hφm := measurable_phaseW h43 ν'
  have hφb := norm_phaseW_le (4 / 3) ν'
  set ψ₁ : X F → ℂ := stripFn D₀ (freq ν') (phaseW (4 / 3) ν') with hψ₁
  set θ₁ : ℂ := ∫ Q in X.box n₁, conj (ψ₁ Q) * X.lift Γ₀ (C5.theta Γ₀ Ψ) Q ∂X.vol F with hθ₁
  have hlimA := tendsto_ray_Afun hG hΓ₀ n₁ (measurable_stripFn hD₀m (freq ν') hφm)
    (norm_stripFn_le _ _ hφb)
  have hlimW := hWray D₀ n₁ _ hD₀m hφm hφb
  have hτ : Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * contSlit a₀ (ray t))
      (𝓝[>] 0) (𝓝 (θ₁ / (κ₀ * Wc D₀ n₁ (phaseW (4 / 3) ν') ν' (4 / 3)))) := by
    have h1 := hlimA.div (hlimW.const_mul κ₀) (mul_ne_zero hk hW0)
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin, hlimW.eventually_ne hW0] with t ht hWt
    have hA := Afun_eq_contSlit Pk hG hz6 hν' hseed hΓ₀ hcoef hD₀m hbn hφm hφb
      (ray_mem_slit ht)
    simp only [Pi.div_apply]
    rw [hA]
    field_simp
  refine ⟨_, hτ, ?_⟩
  intro Γ _ hΓ D κ n φ hc hDm hb hφ hφ1
  have h1 := tendsto_ray_Afun hG hΓ n (measurable_stripFn hDm (freq ν') hφ)
    (norm_stripFn_le D _ hφ1)
  have h2 := ((hτ.const_mul κ).mul (hWray D n φ hDm hφ hφ1))
  refine tendsto_nhds_unique (h1.congr' ?_) h2
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [Afun_eq_contSlit Pk hG hz6 hν' hseed hΓ hc hDm hb hφ hφ1 (ray_mem_slit ht)]
  ring

include Pk hG hz6 in
theorem tendsto_resSlit (hν' : ν' ≠ 0) (hseed : HasSeed Ψ ν' a₀) :
    Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * contSlit a₀ (ray t)) (𝓝[>] 0)
      (𝓝 (resSlit a₀)) := by
  obtain ⟨τ, hτ, -⟩ := exists_res Pk hG hz6 hν' hseed
  rw [resSlit_eq hτ]
  exact hτ

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Linear
/-! # WP-T, file 7: linearity

Twisted level (for the linear combinations of WP-F, which are not genuine sections):
* `eis_add`, `eis_smulFun` (`Re s > 2`); `HasCoefT.add`, `HasCoefT.smulFun`, `HasCoefT.unique`;
* `resSlit_congr`, `resSlit_add`, `resSlit_mul` (function level) and their forms with seeds
  `resSlit_add_of_seed`, `resSlit_mul_of_seed`: `Res(a₀ + b₀) = Res a₀ + Res b₀`,
  `Res(f·a₀) = f(4/3)·Res a₀` for entire `f`.

Genuine level:
* `aSer_add`, `aSer_smulFun`: the Kubota series is linear in `Φ` (`Re s > 2`), read off the
  Fourier coefficients;
* **`tau_add`, `tau_smulFun`, `tau_smul`**.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

/-! ### Function level -/

lemma eventually_ray_mem_slit : ∀ᶠ t : ℝ in 𝓝[>] 0, ray t ∈ E.slit := by
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact ray_mem_slit ht

theorem resSlit_add {a₀ b₀ : ℂ → ℂ} (ha : DifferentiableOn ℂ (contSlit a₀) E.slit)
    (ha' : ∀ s : ℂ, 2 < s.re → contSlit a₀ s = a₀ s)
    (hb : DifferentiableOn ℂ (contSlit b₀) E.slit)
    (hb' : ∀ s : ℂ, 2 < s.re → contSlit b₀ s = b₀ s) {τ σ : ℂ}
    (hτ : Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * contSlit a₀ (ray t)) (𝓝[>] 0)
      (𝓝 τ))
    (hσ : Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * contSlit b₀ (ray t)) (𝓝[>] 0)
      (𝓝 σ)) : resSlit (fun s => a₀ s + b₀ s) = τ + σ := by
  have hu : EqOn (fun s => contSlit a₀ s + contSlit b₀ s) (contSlit fun s => a₀ s + b₀ s)
      E.slit :=
    contSlit_unique (ha.add hb) fun s hs => by rw [ha' s hs, hb' s hs]
  refine resSlit_eq ((hτ.add hσ).congr' ?_)
  filter_upwards [eventually_ray_mem_slit] with t ht
  rw [← hu ht]
  ring

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ}

/-! ### Twisted sections -/

section seeds

variable (Pk : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  {Ψ Ψ' : TSection ι 𝔪} {ν' ν'' : F} {a₀ b₀ : ℂ → ℂ}

include Pk hG hz6 in
/-- `Res (a₀ + b₀) = Res a₀ + Res b₀` for two coefficient series with seeds. -/
theorem resSlit_add_of_seed_oai (hν' : ν' ≠ 0) (hseed : HasSeed Ψ ν' a₀) (hν'' : ν'' ≠ 0)
    (hseed' : HasSeed Ψ' ν'' b₀) :
    resSlit (fun s => a₀ s + b₀ s) = resSlit a₀ + resSlit b₀ :=
  resSlit_add (differentiableOn_contSlit Pk hG hz6 hν' hseed)
    (fun _ hs => contSlit_eq Pk hG hz6 hν' hseed hs)
    (differentiableOn_contSlit Pk hG hz6 hν'' hseed')
    (fun _ hs => contSlit_eq Pk hG hz6 hν'' hseed' hs)
    (tendsto_resSlit Pk hG hz6 hν' hseed) (tendsto_resSlit Pk hG hz6 hν'' hseed')

end seeds

/-! ### Genuine sections -/

end

end ArtinKP.T
end

theorem solution.{u_1} : type_of% @ArtinKP.T.resSlit_add_of_seed_oai.{u_1} := @ArtinKP.T.resSlit_add_of_seed_oai.{u_1}
