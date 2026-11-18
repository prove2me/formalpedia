-- Prove2me | solution 1 for ArtinKP.G2a.exists_major
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:07:54.118056+00:00
-- url     : https://prove2.me/submissions/77b357a5-0c63-41d9-b13c-c14e51cbb72f

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
import Theorems.Thm_ArtinKP_G2a_norm_tau_le

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

theorem besselKer_pos (z t : ℝ) : 0 < besselKer z t := Real.exp_pos _

theorem besselKer_inv (z t : ℝ) : besselKer z t⁻¹ = besselKer z t := by
  unfold besselKer; rw [inv_inv, add_comm]

theorem two_le_add_inv {t : ℝ} (ht : 0 < t) : 2 ≤ t + t⁻¹ := by
  have h : t + t⁻¹ - 2 = (t - 1) ^ 2 * t⁻¹ := by field_simp; ring
  have : 0 ≤ (t - 1) ^ 2 * t⁻¹ := by positivity
  linarith

theorem besselKer_le_exp {z t : ℝ} (hz : 0 ≤ z) (ht : 0 < t) :
    besselKer z t ≤ Real.exp (-(z / 2) * t) := by
  unfold besselKer
  refine Real.exp_le_exp.2 ?_
  have : 0 ≤ z / 2 * t⁻¹ := by positivity
  nlinarith

theorem besselKer_le_shift {z z₀ t : ℝ} (hz : z₀ ≤ z) (ht : 0 < t) :
    besselKer z t ≤ Real.exp (-(z - z₀)) * besselKer z₀ t := by
  unfold besselKer
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h2 := two_le_add_inv ht
  nlinarith [mul_nonneg (sub_nonneg.2 hz) (sub_nonneg.2 h2)]

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

theorem mellinConvergent_besselKer {z : ℝ} (hz : 0 < z) (μ : ℂ) :
    MellinConvergent (fun t => (besselKer z t : ℂ)) μ :=
  mellinConvergent_of_isBigO_rpow (locallyIntegrableOn_besselKer z)
    (besselKer_isBigO_atTop hz (μ.re + 1)) (lt_add_one _)
    (besselKer_isBigO_zero hz (μ.re - 1)) (sub_one_lt _)

/-- `K_{−μ} = K_μ`. -/
theorem besselK_neg (μ : ℂ) (z : ℝ) : besselK (-μ) z = besselK μ z := by
  unfold besselK
  rw [← mellin_comp_inv]
  simp only [besselKer_inv]

/-- The real integrand is integrable. -/
theorem integrableOn_besselKR {z : ℝ} (hz : 0 < z) (μ : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ (μ - 1) * besselKer z t) (Ioi 0) := by
  have h : IntegrableOn (fun t : ℝ => ‖(t : ℂ) ^ ((μ : ℂ) - 1) • (besselKer z t : ℂ)‖) (Ioi 0) :=
    (mellinConvergent_besselKer hz (μ : ℂ)).norm
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht' : (0 : ℝ) < t := ht
  simp only [smul_eq_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (besselKer_pos z t).le]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht']
  simp

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

theorem besselKR_neg (μ z : ℝ) : besselKR (-μ) z = besselKR μ z := by
  have h := besselK_neg (μ : ℂ) z
  rw [← Complex.ofReal_neg, besselK_ofReal, besselK_ofReal] at h
  exact_mod_cast h

theorem besselKR_abs (μ z : ℝ) : besselKR |μ| z = besselKR μ z := by
  rcases abs_choice μ with h | h <;> rw [h]
  exact besselKR_neg μ z

theorem besselKR_pos {z : ℝ} (hz : 0 < z) (μ : ℝ) : 0 < besselKR μ z := by
  unfold besselKR
  refine mul_pos (by norm_num) ?_
  rw [setIntegral_pos_iff_support_of_nonneg_ae ?_ (integrableOn_besselKR hz μ)]
  · have : Function.support (fun t : ℝ => t ^ (μ - 1) * besselKer z t) ∩ Ioi 0 = Ioi 0 := by
      refine inter_eq_right.2 fun t ht => ?_
      exact (mul_pos (Real.rpow_pos_of_pos ht _) (besselKer_pos z t)).ne'
    rw [this]
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (mul_pos (Real.rpow_pos_of_pos ht _) (besselKer_pos z t)).le

/-- `‖K_μ(z)‖ ≤ K_{Re μ}(z)`. -/
theorem norm_besselK_le (μ : ℂ) (z : ℝ) : ‖besselK μ z‖ ≤ besselKR μ.re z := by
  unfold besselK besselKR mellin
  rw [norm_mul]
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [h2]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0 : ℝ) < t := ht
  simp only [smul_eq_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (besselKer_pos z t).le]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht']
  simp

/-- Exponential decay: `K_μ(z) ≤ e^{−(z−z₀)} K_μ(z₀)` for `z ≥ z₀ > 0`. -/
theorem besselKR_le_exp_mul {z z₀ : ℝ} (hz₀ : 0 < z₀) (hz : z₀ ≤ z) (μ : ℝ) :
    besselKR μ z ≤ Real.exp (-(z - z₀)) * besselKR μ z₀ := by
  unfold besselKR
  rw [mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [← integral_const_mul]
  refine setIntegral_mono_on (integrableOn_besselKR (hz₀.trans_le hz) μ)
    ((integrableOn_besselKR hz₀ μ).const_mul _) measurableSet_Ioi fun t ht => ?_
  have ht' : (0 : ℝ) < t := ht
  calc t ^ (μ - 1) * besselKer z t ≤ t ^ (μ - 1) * (Real.exp (-(z - z₀)) * besselKer z₀ t) :=
        mul_le_mul_of_nonneg_left (besselKer_le_shift hz ht') (Real.rpow_nonneg ht'.le _)
    _ = Real.exp (-(z - z₀)) * (t ^ (μ - 1) * besselKer z₀ t) := by ring

/-- `K_μ(z) ≤ ½ Γ(μ) (z/2)^{−μ}` for `μ > 0`, `z > 0`. -/
theorem besselKR_le_gamma_of_pos {μ z : ℝ} (hμ : 0 < μ) (hz : 0 < z) :
    besselKR μ z ≤ 1 / 2 * (Real.Gamma μ * (z / 2) ^ (-μ)) := by
  unfold besselKR
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hI : IntegrableOn (fun t : ℝ => t ^ (μ - 1) * Real.exp (-(z / 2 * t))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := μ - 1) (b := z / 2)
      (by linarith) one_pos (half_pos hz)
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, neg_mul]
  have hE : ∫ t in Ioi (0 : ℝ), t ^ (μ - 1) * Real.exp (-(z / 2 * t)) =
      Real.Gamma μ * (z / 2) ^ (-μ) := by
    rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hμ (half_pos hz), one_div,
      Real.inv_rpow (half_pos hz).le, Real.rpow_neg (half_pos hz).le, mul_comm]
  rw [← hE]
  refine setIntegral_mono_on (integrableOn_besselKR hz μ) hI measurableSet_Ioi fun t ht => ?_
  have ht' : (0 : ℝ) < t := ht
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ht'.le _)
  have := besselKer_le_exp hz.le ht'
  rwa [neg_mul] at this

/-- Small-argument bound: `K_μ(z) ≤ ½ Γ(|μ|) (z/2)^{−|μ|}` for `μ ≠ 0`, `z > 0`. -/
theorem besselKR_le_gamma {μ z : ℝ} (hμ : μ ≠ 0) (hz : 0 < z) :
    besselKR μ z ≤ 1 / 2 * (Real.Gamma |μ| * (z / 2) ^ (-|μ|)) := by
  rw [← besselKR_abs]
  exact besselKR_le_gamma_of_pos (abs_pos.2 hμ) hz

theorem exp_neg_le_rpow_neg {N z : ℝ} (_hN : 0 ≤ N) (hz : 1 ≤ z) :
    Real.exp (-z) ≤ (Nat.ceil N).factorial * z ^ (-N) := by
  have hz0 : 0 < z := by linarith
  set m := Nat.ceil N
  have h1 : z ^ N ≤ z ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hz (Nat.le_ceil _)
  rw [Real.rpow_natCast] at h1
  have h2 : z ^ m / m.factorial ≤ Real.exp z := Real.pow_div_factorial_le_exp z hz0.le m
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  rw [div_le_iff₀ hf] at h2
  have h3 : z ^ N ≤ Real.exp z * m.factorial := h1.trans h2
  rw [Real.exp_neg, Real.rpow_neg hz0.le, inv_le_iff_one_le_mul₀ (Real.exp_pos z)]
  have hzN : 0 < z ^ N := Real.rpow_pos_of_pos hz0 _
  rw [show (m.factorial : ℝ) * (z ^ N)⁻¹ * Real.exp z = (Real.exp z * m.factorial) * (z ^ N)⁻¹
    by ring, ← div_eq_mul_inv, le_div_iff₀ hzN]
  linarith

/-- The two-sided bound used for Fourier series: uniformly for `a ≤ |μ| ≤ M ≤ N`,
`K_μ(z) ≤ C min(z^{−|μ|}, z^{−N})` for all `z > 0`. -/
theorem besselKR_le_min {a M N : ℝ} (ha : 0 < a) (hMN : M ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : ℝ, a ≤ |μ| → |μ| ≤ M → ∀ z : ℝ, 0 < z →
      besselKR μ z ≤ C * min (z ^ (-|μ|)) (z ^ (-N)) := by
  have hcont : ContinuousOn Real.Gamma (Icc a M) := fun x hx =>
    (Real.differentiableAt_Gamma fun m => by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have := hx.1
      intro h; linarith).continuousAt.continuousWithinAt
  obtain ⟨G, hG⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  set G' := max G 1
  have hG' : ∀ x ∈ Icc a M, Real.Gamma x ≤ G' := fun x hx =>
    ((Real.le_norm_self _).trans (hG x hx)).trans (le_max_left _ _)
  have hG'0 : 0 < G' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set B : ℝ := 1 / 2 * (G' * 2 ^ M)
  have hB : 0 < B := by positivity
  set F : ℝ := Real.exp 1 * (Nat.ceil N).factorial
  have hF : 0 < F := by positivity
  have hF1 : 1 ≤ F := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h2 : (1 : ℝ) ≤ (Nat.ceil N).factorial := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ F := mul_le_mul h1 h2 (by norm_num) (by positivity)
  refine ⟨B * F, by positivity, fun μ hμa hμM z hz => ?_⟩
  have hμ0 : μ ≠ 0 := abs_pos.1 (ha.trans_le hμa)
  have hN : 0 ≤ N := (abs_nonneg μ).trans (hμM.trans hMN)
  -- the bound `K_μ(z) ≤ B z^{-|μ|}`
  have hsmall : ∀ z : ℝ, 0 < z → besselKR μ z ≤ B * z ^ (-|μ|) := by
    intro z hz
    refine (besselKR_le_gamma hμ0 hz).trans ?_
    have e : (z / 2) ^ (-|μ|) = 2 ^ |μ| * z ^ (-|μ|) := by
      rw [Real.div_rpow hz.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) |μ|]
      field_simp
    rw [e]
    have h2 : (2 : ℝ) ^ |μ| ≤ 2 ^ M := Real.rpow_le_rpow_of_exponent_le (by norm_num) hμM
    have hz' : 0 ≤ z ^ (-|μ|) := Real.rpow_nonneg hz.le _
    have hg := hG' |μ| ⟨hμa, hμM⟩
    have hg0 : 0 ≤ Real.Gamma |μ| := (Real.Gamma_pos_of_pos (ha.trans_le hμa)).le
    calc 1 / 2 * (Real.Gamma |μ| * (2 ^ |μ| * z ^ (-|μ|)))
        ≤ 1 / 2 * (G' * (2 ^ M * z ^ (-|μ|))) := by gcongr
      _ = B * z ^ (-|μ|) := by simp only [B]; ring
  rcases le_total z 1 with h1 | h1
  · have hmin : min (z ^ (-|μ|)) (z ^ (-N)) = z ^ (-|μ|) :=
      min_eq_left (Real.rpow_le_rpow_of_exponent_ge hz h1 (by linarith [hμM.trans hMN]))
    rw [hmin]
    refine (hsmall z hz).trans ?_
    have hz' : 0 ≤ z ^ (-|μ|) := Real.rpow_nonneg hz.le _
    calc B * z ^ (-|μ|) = B * 1 * z ^ (-|μ|) := by ring
      _ ≤ B * F * z ^ (-|μ|) := by gcongr
  · have hmin : min (z ^ (-|μ|)) (z ^ (-N)) = z ^ (-N) :=
      min_eq_right (Real.rpow_le_rpow_of_exponent_le h1 (by linarith [hμM.trans hMN]))
    rw [hmin]
    have hd := besselKR_le_exp_mul one_pos h1 μ
    have h1' := hsmall 1 one_pos
    rw [Real.one_rpow, mul_one] at h1'
    have he : Real.exp (-(z - 1)) = Real.exp 1 * Real.exp (-z) := by
      rw [← Real.exp_add]; congr 1; ring
    have hx := exp_neg_le_rpow_neg hN h1
    have hK0 := (besselKR_pos one_pos μ).le
    calc besselKR μ z ≤ Real.exp (-(z - 1)) * besselKR μ 1 := hd
      _ ≤ Real.exp (-(z - 1)) * B := by gcongr
      _ = Real.exp 1 * Real.exp (-z) * B := by rw [he]
      _ ≤ Real.exp 1 * ((Nat.ceil N).factorial * z ^ (-N)) * B := by gcongr
      _ = B * F * z ^ (-N) := by simp only [F]; ring

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
-- module Solutions.Artin.KP.G2a_Arch
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-G2a, file 1: the archimedean majorant

For `s = 4/3` the Jacquet integral is `c·(2π|ν|)^{1/3}·v·K_{1/3}(4π|ν|v)`; with the factor
`|ν|^{2/3}` that Theorem E supplies (`N_∞(ν)^{1/3}`) it is a function of `z = 4π|ν|v`,
`z·K_{1/3}(z)`, bounded and rapidly decreasing.

* `jac_bound`: one place, `|ν|^{2/3}(1+|ν|)^p·|jacquet (4/3) ν v| ≤ K·(1+|ν|)^{-4}` uniformly for
  `v ∈ [1/(n₀+1), n₀+1]`.
* `Winf_bound`: the product over the places, on `RF.vBox F n₀`.
-/

open scoped ComplexConjugate Topology
open MeasureTheory Set NumberField Filter

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.K ArtinKP.B ArtinKP.RF

noncomputable section

/-- `z·K_{1/3}(z) ≤ C` and `≤ C·z^{-q}` for every `q`. -/
theorem zK_bound (q : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 0 < z →
    z * besselKR (1 / 3) z ≤ C ∧ z * besselKR (1 / 3) z ≤ C * (z ^ q)⁻¹ := by
  obtain ⟨C, hC, h⟩ := besselKR_le_min (a := 1 / 3) (M := 1 / 3) (N := (q : ℝ) + 1)
    (by norm_num) (by have : (0 : ℝ) ≤ q := Nat.cast_nonneg q; linarith)
  have habs : |(1 / 3 : ℝ)| = 1 / 3 := abs_of_pos (by norm_num)
  have key : ∀ z : ℝ, 0 < z → z * besselKR (1 / 3) z ≤ C * z ^ (2 / 3 : ℝ) ∧
      z * besselKR (1 / 3) z ≤ C * (z ^ q)⁻¹ := by
    intro z hz
    have h1 := h (1 / 3) (by rw [habs]) (by rw [habs]) z hz
    rw [habs] at h1
    constructor
    · have h2 := h1.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hC.le)
      calc z * besselKR (1 / 3) z ≤ z * (C * z ^ (-(1 / 3 : ℝ))) :=
            mul_le_mul_of_nonneg_left h2 hz.le
        _ = C * (z ^ (1 : ℝ) * z ^ (-(1 / 3 : ℝ))) := by rw [Real.rpow_one]; ring
        _ = C * z ^ (2 / 3 : ℝ) := by rw [← Real.rpow_add hz]; norm_num
    · have h2 := h1.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)
      calc z * besselKR (1 / 3) z ≤ z * (C * z ^ (-((q : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left h2 hz.le
        _ = C * (z ^ (1 : ℝ) * z ^ (-((q : ℝ) + 1))) := by rw [Real.rpow_one]; ring
        _ = C * (z ^ q)⁻¹ := by
            rw [← Real.rpow_add hz, show (1 : ℝ) + -((q : ℝ) + 1) = -(q : ℝ) by ring,
              Real.rpow_neg hz.le, Real.rpow_natCast]
  refine ⟨C, hC, fun z hz => ⟨?_, (key z hz).2⟩⟩
  rcases le_total z 1 with h1 | h1
  · refine (key z hz).1.trans ?_
    have : z ^ (2 / 3 : ℝ) ≤ 1 := Real.rpow_le_one hz.le h1 (by norm_num)
    nlinarith
  · refine (key z hz).2.trans ?_
    have : (z ^ q)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ h1)
    nlinarith

/-- The norm of the Jacquet integral at `4/3`. -/
theorem norm_jacquet_le {ν : ℂ} (hν : ν ≠ 0) {v : ℝ} (hv : 0 < v) :
    ‖jacquet (4 / 3) ν v‖ ≤ ‖(2 * Real.pi : ℂ) / Complex.Gamma (4 / 3)‖ *
      (2 * Real.pi * ‖ν‖) ^ (1 / 3 : ℝ) * v * besselKR (1 / 3) (4 * Real.pi * ‖ν‖ * v) := by
  have hn : 0 < ‖ν‖ := norm_pos_iff.mpr hν
  rw [jacquet_eq (4 / 3) (by norm_num) hν hv, norm_mul, norm_mul, norm_mul]
  have h1 : ‖(((2 * Real.pi * ‖ν‖ : ℝ)) : ℂ) ^ ((4 / 3 : ℂ) - 1)‖
      = (2 * Real.pi * ‖ν‖) ^ (1 / 3 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    congr 1
    norm_num
  have h2 : ‖besselK ((4 / 3 : ℂ) - 1) (4 * Real.pi * ‖ν‖ * v)‖
      ≤ besselKR (1 / 3) (4 * Real.pi * ‖ν‖ * v) := by
    refine (norm_besselK_le _ _).trans (le_of_eq ?_)
    congr 1
    norm_num
  have h3 : ‖((v : ℝ) : ℂ)‖ = v := by rw [Complex.norm_real, Real.norm_of_nonneg hv.le]
  rw [h1, h3]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **One place.** -/
theorem jac_bound (p n₀ : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ ν : ℂ, ν ≠ 0 → ∀ v : ℝ,
    1 / ((n₀ : ℝ) + 1) ≤ v → v ≤ (n₀ : ℝ) + 1 →
    ‖ν‖ ^ (2 / 3 : ℝ) * (1 + ‖ν‖) ^ p * ‖jacquet (4 / 3) ν v‖ ≤ K * ((1 + ‖ν‖) ^ 4)⁻¹ := by
  obtain ⟨C, hC, hz⟩ := zK_bound (p + 4)
  set c₁ : ℝ := ‖(2 * Real.pi : ℂ) / Complex.Gamma (4 / 3)‖ * (2 * Real.pi) ^ (1 / 3 : ℝ)
    * (4 * Real.pi)⁻¹ with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  set c : ℝ := 4 * Real.pi / ((n₀ : ℝ) + 1) with hc
  have hc0 : 0 < c := by positivity
  refine ⟨c₁ * (C * 2 ^ (p + 4) * (1 + (c ^ (p + 4))⁻¹)), by positivity, fun ν hν v hv1 hv2 => ?_⟩
  have hn : 0 < ‖ν‖ := norm_pos_iff.mpr hν
  have hv : 0 < v := lt_of_lt_of_le (by positivity) hv1
  set z : ℝ := 4 * Real.pi * ‖ν‖ * v with hzdef
  have hz0 : 0 < z := by positivity
  have hzc : c * ‖ν‖ ≤ z := by
    rw [hc, hzdef]
    have : 4 * Real.pi * ‖ν‖ * (1 / ((n₀ : ℝ) + 1)) ≤ 4 * Real.pi * ‖ν‖ * v :=
      mul_le_mul_of_nonneg_left hv1 (by positivity)
    calc 4 * Real.pi / ((n₀ : ℝ) + 1) * ‖ν‖ = 4 * Real.pi * ‖ν‖ * (1 / ((n₀ : ℝ) + 1)) := by ring
      _ ≤ _ := this
  -- reduce to `z K(z)`
  have hj := norm_jacquet_le hν hv
  have e1 : ‖ν‖ ^ (2 / 3 : ℝ) * (‖(2 * Real.pi : ℂ) / Complex.Gamma (4 / 3)‖ *
      (2 * Real.pi * ‖ν‖) ^ (1 / 3 : ℝ) * v * besselKR (1 / 3) z)
      = c₁ * (z * besselKR (1 / 3) z) := by
    rw [Real.mul_rpow (by positivity) hn.le, hc₁, hzdef]
    have : ‖ν‖ ^ (2 / 3 : ℝ) * ‖ν‖ ^ (1 / 3 : ℝ) = ‖ν‖ := by
      rw [← Real.rpow_add hn]; norm_num
    have hpi : (4 * Real.pi) ≠ 0 := by positivity
    calc _ = ‖(2 * Real.pi : ℂ) / Complex.Gamma (4 / 3)‖ * (2 * Real.pi) ^ (1 / 3 : ℝ) *
          (‖ν‖ ^ (2 / 3 : ℝ) * ‖ν‖ ^ (1 / 3 : ℝ)) * v * besselKR (1 / 3) (4 * Real.pi * ‖ν‖ * v) := by
          ring
      _ = _ := by rw [this]; field_simp
  have hmain : (1 + ‖ν‖) ^ (p + 4) * (z * besselKR (1 / 3) z)
      ≤ C * 2 ^ (p + 4) * (1 + (c ^ (p + 4))⁻¹) := by
    have hK0 : 0 ≤ z * besselKR (1 / 3) z := mul_nonneg hz0.le (besselKR_pos hz0 _).le
    rcases le_total ‖ν‖ 1 with h1 | h1
    · have h2 : (1 + ‖ν‖) ^ (p + 4) ≤ 2 ^ (p + 4) :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      have h3 := (hz z hz0).1
      have h4 : (0 : ℝ) ≤ (c ^ (p + 4))⁻¹ := by positivity
      calc (1 + ‖ν‖) ^ (p + 4) * (z * besselKR (1 / 3) z) ≤ 2 ^ (p + 4) * C :=
            mul_le_mul h2 h3 hK0 (by positivity)
        _ ≤ C * 2 ^ (p + 4) * (1 + (c ^ (p + 4))⁻¹) := by
            have : (0 : ℝ) ≤ C * 2 ^ (p + 4) := by positivity
            nlinarith
    · have h2 : (1 + ‖ν‖) ^ (p + 4) ≤ (2 * ‖ν‖) ^ (p + 4) :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      have h3 := (hz z hz0).2
      have h4 : (z ^ (p + 4))⁻¹ ≤ ((c * ‖ν‖) ^ (p + 4))⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hzc _)
      calc (1 + ‖ν‖) ^ (p + 4) * (z * besselKR (1 / 3) z)
          ≤ (2 * ‖ν‖) ^ (p + 4) * (C * ((c * ‖ν‖) ^ (p + 4))⁻¹) :=
            mul_le_mul h2 (h3.trans (mul_le_mul_of_nonneg_left h4 hC.le)) hK0 (by positivity)
        _ = C * 2 ^ (p + 4) * (c ^ (p + 4))⁻¹ := by
            rw [mul_pow, mul_pow]
            have : ‖ν‖ ^ (p + 4) ≠ 0 := by positivity
            field_simp
        _ ≤ C * 2 ^ (p + 4) * (1 + (c ^ (p + 4))⁻¹) := by
            have : (0 : ℝ) ≤ C * 2 ^ (p + 4) := by positivity
            nlinarith
  have h14 : (0 : ℝ) < (1 + ‖ν‖) ^ 4 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ h14]
  calc ‖ν‖ ^ (2 / 3 : ℝ) * (1 + ‖ν‖) ^ p * ‖jacquet (4 / 3) ν v‖ * (1 + ‖ν‖) ^ 4
      = (1 + ‖ν‖) ^ (p + 4) * (‖ν‖ ^ (2 / 3 : ℝ) * ‖jacquet (4 / 3) ν v‖) := by rw [pow_add]; ring
    _ ≤ (1 + ‖ν‖) ^ (p + 4) * (c₁ * (z * besselKR (1 / 3) z)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← e1]
        exact mul_le_mul_of_nonneg_left hj (by positivity)
    _ = c₁ * ((1 + ‖ν‖) ^ (p + 4) * (z * besselKR (1 / 3) z)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmain hc₁0

variable {F : Type*} [Field F] [NumberField F]

/-- **All places**: on `vBox F n₀`,
`∏_w |ν|_w^{2/3}(1+|ν|_w)^p · |W_{4/3}(ν; v)| ≤ K ∏_w (1+|ν|_w)^{-4}`. -/
theorem Winf_bound (p n₀ : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ ν : F, ν ≠ 0 →
    ∀ v ∈ vBox F n₀,
    (∏ w : InfinitePlace F, (w ν) ^ (2 / 3 : ℝ) * (1 + w ν) ^ p) * ‖Winf (4 / 3) ν v‖
      ≤ K * ∏ w : InfinitePlace F, ((1 + w ν) ^ 4)⁻¹ := by
  obtain ⟨K, hK, h⟩ := jac_bound p n₀
  refine ⟨K ^ Fintype.card (InfinitePlace F), by positivity, fun ν hν v hv => ?_⟩
  unfold Winf
  rw [norm_prod, ← Finset.prod_mul_distrib, ← Finset.card_univ, ← Finset.prod_const,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun w _ => by positivity) fun w _ => ?_
  have hne : -(w.embedding ν) ≠ 0 := neg_ne_zero.mpr ((map_ne_zero _).mpr hν)
  have := h (-(w.embedding ν)) hne (v w) (hv w).1 (hv w).2
  rwa [norm_neg, InfinitePlace.norm_embedding_eq] at this

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.T12.L3X_Meas
/-! # L3X_Meas: sheet measures on the model `SModel 𝔪 k` of `F_S^× / U`

* `lnorm y = Σ_w log|y_w|_w + log |y_f|_{S_f}` (the log of the `S`-norm).
* For a place `w₀`, the base space `SFin × (ℝ^{W∖w₀} × (ℝ/2πℤ)^W)` carries counting ⊗ Lebesgue ⊗
  Haar, and `slice w₀ a` sends it onto the sheet `{lnorm = a}`, solving for the `w₀` log-coordinate.
* `shMeasure w₀ a` is the push-forward: the sheet measure on `X_{e^a}`.
* Translation by `d` maps `shMeasure a` to `shMeasure (a + lnorm d)`; negation maps `shMeasure a` to
  `shMeasure (-a)`; moving the `w₀` coordinate by `t` moves the slice from `a` to `a + t`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-! ### The finite norm -/

theorem SFin.norm_mk (x : Fˣ) :
    (SFin.mk 𝔪 k x).norm = ∏ᶠ v ∈ placesOf 𝔪, NumberField.HeightOneSpectrum.adicAbv F v (x : F) :=
  rfl

theorem SFin.mk_surjective : Function.Surjective (SFin.mk 𝔪 k) := by
  intro y
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
  exact ⟨x, by simp only [SFin.mk, hx]; rfl⟩


theorem SFin.norm_mk_eq_prod (h𝔪 : 𝔪 ≠ ⊥) (x : Fˣ) :
    (SFin.mk 𝔪 k x).norm =
      ∏ v ∈ (finite_placesOf h𝔪).toFinset, NumberField.HeightOneSpectrum.adicAbv F v (x : F) := by
  rw [SFin.norm_mk, finprod_mem_eq_finite_toFinset_prod _ (finite_placesOf h𝔪)]

theorem SFin.norm_mk_pos (h𝔪 : 𝔪 ≠ ⊥) (x : Fˣ) : 0 < (SFin.mk 𝔪 k x).norm := by
  rw [SFin.norm_mk_eq_prod h𝔪]
  exact Finset.prod_pos fun v _ => (AbsoluteValue.pos_iff _).2 x.ne_zero

theorem SFin.norm_pos (h𝔪 : 𝔪 ≠ ⊥) (y : SFin 𝔪 k) : 0 < y.norm := by
  obtain ⟨x, rfl⟩ := SFin.mk_surjective y
  exact SFin.norm_mk_pos h𝔪 x

/-! ### `lnorm` -/

/-! ### Slices -/


/-! ### Measure preservation -/

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.T12.L3P_Val
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# L3P_Val: valuations as counts of principal fractional ideals

For `x ≠ 0` in a number field, `v.valuation x = exp (−count_v (x))`, where
`count_v (x) = FractionalIdeal.count F v (spanSingleton x)`. Membership in a nonzero fractional
ideal is a comparison of counts.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped nonZeroDivisors Classical

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F]

/-! ### The places of `S` -/

variable {𝔪 : Ideal (𝓞 F)}

variable [Fintype (SP 𝔪)]

omit [Fintype (SP 𝔪)] in
theorem one_lt_qS (v : SP 𝔪) : 1 < qS v := by
  rw [qS]
  have h0 : Ideal.absNorm v.1.asIdeal ≠ 0 := by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff]; exact v.1.ne_bot
  have h1 : Ideal.absNorm v.1.asIdeal ≠ 1 := by
    rw [ne_eq, Ideal.absNorm_eq_one_iff]; exact v.1.isPrime.ne_top
  have : 2 ≤ Ideal.absNorm v.1.asIdeal := by omega
  exact_mod_cast this

theorem NN_eq_prod {S : Type*} [Fintype S] (q : S → ℝ) (hq : ∀ v, 0 < q v) (k : S → ℤ) :
    NN q k = ∏ v, q v ^ k v := by
  rw [NN, Real.exp_sum]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [lq, mul_comm, ← Real.rpow_intCast, Real.rpow_def_of_pos (hq v)]

theorem absNorm_Pk (k : SP 𝔪 → ℤ) :
    ((FractionalIdeal.absNorm ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
      FractionalIdeal (𝓞 F)⁰ F) : ℚ) : ℝ) = NN (qS (𝔪 := 𝔪)) k := by
  rw [coe_Pk, map_prod, NN_eq_prod qS (fun v => (one_lt_qS v).trans' one_pos)]
  push_cast
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_zpow₀, coeIdeal_absNorm]
  push_cast; rfl

/-- `|N m| = N 𝔟 · N(P^{val_S m})`. -/
theorem abs_norm_eq {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) {m : SInt 𝔪}
    (hm : Ideal.span {m} = 𝔟.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    ((|Algebra.norm ℚ (m : F)| : ℚ) : ℝ) = (Ideal.absNorm 𝔟 : ℝ) * NN (qS (𝔪 := 𝔪)) (valS (m : F)) := by
  rw [← absNorm_span_singleton (R := 𝓞 F), spanSingleton_eq_mul_Pk h𝔟 hm, map_mul,
    coeIdeal_absNorm, Rat.cast_mul, absNorm_Pk]
  push_cast; rfl

/-! ### Units, the different, and the trace dual -/

end ArtinPrimitiveRoots.L3P
end

section
-- module Solutions.Artin.T12.L3X_Emb
/-! # L3X_Emb: the embedding `F^× → SModel 𝔪 k`

* `sEmb` is a homomorphism on `F^×`.
* The `v`-adic absolute value is `q_v^{-ord_v}`; the finite norm of `[x]` is `∏_{v∈S_f} q_v^{-ord_v x}`.
* The product formula: `lnorm (sEmb m) = log N 𝔟` for an `S`-integer `m` generating the exterior
  ideal `𝔟 R`; in particular `lnorm (sEmb ε) = 0` for `S`-units.
* Valuations at `S_f` descend to `SFin`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory IsDedekindDomain

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

theorem sEmb_of_ne {x : F} (hx : x ≠ 0) :
    sEmb 𝔪 k x = (fun w => (w.mult : ℝ) * Real.log (w x),
      fun w => ((Complex.arg (w.embedding x) : ℝ) : AddCircle (2 * Real.pi)),
      SFin.mk 𝔪 k (Units.mk0 x hx)) := by
  rw [sEmb, dif_neg hx]

theorem sEmb_fin {x : F} (hx : x ≠ 0) : (sEmb 𝔪 k x).2.2 = SFin.mk 𝔪 k (Units.mk0 x hx) := by
  rw [sEmb_of_ne hx]

theorem sEmb_fst {x : F} (hx : x ≠ 0) (w : InfinitePlace F) :
    (sEmb 𝔪 k x).1 w = (w.mult : ℝ) * Real.log (w x) := by
  rw [sEmb_of_ne hx]

/-! ### Absolute values and valuations -/

theorem adicAbv_eq (v : HeightOneSpectrum (𝓞 F)) {x : F} (hx : x ≠ 0) :
    NumberField.HeightOneSpectrum.adicAbv F v x =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-L3P.ordv v x) := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def, L3P.valuation_eq_exp_neg_ordv v hx,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, WithZero.toAdd_unzero_eq_log,
    WithZero.log_exp]
  simp [zpow_neg]

theorem log_SFin_norm_mk (h𝔪 : 𝔪 ≠ ⊥) {x : F} (hx : x ≠ 0) :
    letI : Fintype (L3P.SP 𝔪) := (finite_placesOf h𝔪).fintype
    Real.log (SFin.mk 𝔪 k (Units.mk0 x hx)).norm =
      -∑ v : L3P.SP 𝔪, (L3P.ordv v.1 x : ℝ) * Real.log (Ideal.absNorm v.1.asIdeal : ℝ) := by
  letI : Fintype (L3P.SP 𝔪) := (finite_placesOf h𝔪).fintype
  rw [SFin.norm_mk_eq_prod h𝔪]
  have hq : ∀ v : HeightOneSpectrum (𝓞 F), 0 < (Ideal.absNorm v.asIdeal : ℝ) := fun v => by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (by omega : 0 < Ideal.absNorm v.asIdeal)
  rw [Real.log_prod (fun v _ => by
    rw [Units.val_mk0, adicAbv_eq v hx]; exact (zpow_pos (hq v) _).ne')]
  rw [← Finset.sum_neg_distrib]
  rw [Finset.sum_subtype (finite_placesOf h𝔪).toFinset (p := fun v => v ∈ placesOf 𝔪)
    (by simp)]
  convert Finset.sum_congr rfl fun (v : L3P.SP 𝔪) _ => (show
    Real.log ((NumberField.HeightOneSpectrum.adicAbv F v.1) ((Units.mk0 x hx : Fˣ) : F)) =
      -((L3P.ordv v.1 x : ℝ) * Real.log (Ideal.absNorm v.1.asIdeal : ℝ)) by
    rw [Units.val_mk0, adicAbv_eq v.1 hx, Real.log_zpow]; push_cast; ring)

/-- The product formula on the model. -/
theorem lnorm_sEmb_gen (h𝔪 : 𝔪 ≠ ⊥) {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) {m : SInt 𝔪}
    (hm : Ideal.span {m} = 𝔟.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    lnorm (sEmb 𝔪 k (m : F)) = Real.log (Ideal.absNorm 𝔟 : ℝ) := by
  letI : Fintype (L3P.SP 𝔪) := (finite_placesOf h𝔪).fintype
  have hm0 : (m : F) ≠ 0 := L3P.ne_zero_of_span_eq h𝔟 hm
  have hN := L3P.abs_norm_eq (𝔪 := 𝔪) h𝔟 hm
  have hinf : ∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log (w (m : F)) =
      Real.log (((|Algebra.norm ℚ (m : F)| : ℚ) : ℝ)) := by
    rw [← InfinitePlace.prod_eq_abs_norm, Real.log_prod (fun w _ =>
      pow_ne_zero _ ((map_ne_zero w).2 hm0))]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Real.log_pow]
  have h𝔟0 : (0 : ℝ) < Ideal.absNorm 𝔟 := by
    have : Ideal.absNorm 𝔟 ≠ 0 := by
      rw [ne_eq, Ideal.absNorm_eq_zero_iff]; exact h𝔟.1
    exact_mod_cast Nat.pos_of_ne_zero this
  rw [lnorm, sEmb_of_ne hm0]
  simp only
  rw [hinf, log_SFin_norm_mk h𝔪 hm0, hN, L3P.NN, Real.log_mul h𝔟0.ne' (Real.exp_pos _).ne',
    Real.log_exp]
  simp only [L3P.lq, L3P.qS, L3P.valS]
  ring

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.KP.H0_Row
/-! # WP-H0, file 3: the coordinate dictionary, part 1 — rows and frequencies

`(z, γ) ↦ γ · rowElt g z` is a bijection `RowClass 𝔪 × U_S⁶ ≃ R ∖ {0}` (`rowEquiv`), so each of the
two `∑'` of the frozen goal is a sum over `ν ∈ R ∖ 0` (`tsum_forward`, `tsum_reflected`, with the
exact summands of the goal). `rowOf ν` is the row class of `ν`: its ideal is the unique exterior
ideal `𝔷` with `𝔷R = νR` (`span_eq_map_rowOf`, `rowOf_ideal_unique`), its multiplicities are the
valuations of `ν` (`count_rowOf`), and it only depends on `ν` modulo `U_S⁶` (`rowOf_gam_mul`). -/

namespace ArtinKP.H0

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

section

variable (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪)
include h𝔪

/-- The ideal of `rowOf ν` generates `νR`. -/
theorem span_eq_map_rowOf (ν : {ν : SInt 𝔪 // ν ≠ 0}) :
    Ideal.span {(ν : SInt 𝔪)} = (rowOf h𝔪 g ν).1.1.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  have : Fintype (L3P.SP 𝔪) := (L3X.finite_placesOf h𝔪).fintype
  have h : (ν : SInt 𝔪) = rowSInt g ((rowEquiv h𝔪 g).symm ν) :=
    (congrArg Subtype.val ((rowEquiv h𝔪 g).apply_symm_apply ν)).symm
  rw [h, rowSInt_eq_par]
  exact L3P.span_unit_mul_gen g _ _

/-! ### Reindexing the two sums of the frozen goal -/

end

end

end ArtinKP.H0
end

section
-- module Solutions.Artin.KP.H0_Coord
/-! # WP-H0, file 4: the coordinate dictionary, part 2 — `SFin`, `sEmb`, `fp`, `Fm`

* `SFin`: `SFin.mk x = 0 ↔ x ∈ SLevel` (`= F^× ∩ U_k`), equality of classes, and weak approximation
  in the form needed: every class of `SFin 𝔪 k` is the class of a nonzero `S`-integer
  (`exists_sInt_rep`); `mem_SLevel_of_sub_one_mem`: `d ≡ 1 mod 𝔪^{k+1}` lies in `SLevel 𝔪 k`.
* `fpF_sEmb_add`: `fp (sEmb ν + y)` is the indicator of `[ν] + y_f = 0` (i.e. `ν·y_f ∈ U_k`)
  times `∏_w ω_{m_w}(ν_w) ω_{m_w}(y_w) κ(|ν|_w · e^{x_w})`.
* `FmOf_sEmb_sub`: the product-form `Fm` at `sEmb ν − y`.
* rotation covariance: `fpF_add_rot`, `FmOf_sub_rot`. -/

namespace ArtinKP.H0

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots FractionalIdeal

set_option linter.unusedSectionVars false

open scoped Classical nonZeroDivisors

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-! ### `SFin` -/

theorem SFin_mk_eq_mk_iff (x y : Fˣ) :
    SFin.mk 𝔪 k x = SFin.mk 𝔪 k y ↔ x⁻¹ * y ∈ SLevel 𝔪 k :=
  Additive.ofMul.injective.eq_iff.trans QuotientGroup.eq

/-! ### `SFinCls` -/

/-! ### Angular characters and rotations -/

/-! ### The two functions at `sEmb ν ± y` -/

end

end ArtinKP.H0
end

section
-- module Solutions.Artin.KP.H_Grid
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-HA, file 1: a grid bound for sums over separated point sets (pure analysis)

`grid_sum`: let `e : T → (W → ℂ)` (`W` finite) be such that two distinct points never lie in a
common cell of mesh `h` (in every real and imaginary coordinate). Then

  `∑_{t ∈ T} ∏_w (1 + ‖e t w‖)⁻⁴ ≤ (2 (1 + ζ₂ / h²))^{2 #W}`,

with absolute convergence. No measure theory: the points are injected into the grid
`(W × Bool → Bool × ℕ)` (sign and `⌊|x| / h⌋`), and the sum over the grid is a product of
one-dimensional sums (`pi_prod_summable`). -/

namespace ArtinKP.H

open Finset

/-- A sum of products over a finite index set is bounded by the product of the sums. -/
theorem pi_prod_summable {I : Type*} [Fintype I] [DecidableEq I] {β : Type*} (f : I → β → ℝ)
    (hf0 : ∀ i b, 0 ≤ f i b) (hf : ∀ i, Summable (f i)) :
    Summable (fun a : I → β => ∏ i, f i (a i)) ∧
      ∑' a : I → β, ∏ i, f i (a i) ≤ ∏ i, ∑' b, f i b := by
  classical
  have key : ∀ s : Finset (I → β), ∑ a ∈ s, ∏ i, f i (a i) ≤ ∏ i, ∑' b, f i b := by
    intro s
    set t : I → Finset β := fun i => s.image (fun a => a i)
    have hsub : s ⊆ Fintype.piFinset t := by
      intro a ha
      rw [Fintype.mem_piFinset]
      intro i
      exact Finset.mem_image_of_mem (fun a => a i) ha
    calc ∑ a ∈ s, ∏ i, f i (a i) ≤ ∑ a ∈ Fintype.piFinset t, ∏ i, f i (a i) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun a _ _ => Finset.prod_nonneg fun i _ => hf0 i _)
      _ = ∏ i, ∑ b ∈ t i, f i b := (Finset.prod_univ_sum t f).symm
      _ ≤ ∏ i, ∑' b, f i b := Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun b _ => hf0 i b)
          (fun i _ => (hf i).sum_le_tsum _ (fun b _ => hf0 i b))
  have hs : Summable (fun a : I → β => ∏ i, f i (a i)) :=
    summable_of_sum_le (fun a => Finset.prod_nonneg fun i _ => hf0 i (a i)) key
  exact ⟨hs, hs.tsum_le_of_sum_le key⟩

theorem summable_zeta2 : Summable (fun j : ℕ => (((j : ℝ) + 1) ^ 2)⁻¹) := by
  have h := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
  refine h.congr fun j => ?_
  push_cast
  rw [one_div]

theorem zeta2_nonneg : 0 ≤ zeta2 := tsum_nonneg fun j => by positivity

/-- The one-dimensional cell sum. -/
theorem summable_cell {h : ℝ} (hh : 0 < h) :
    Summable (fun j : ℕ => ((1 + h * (j : ℝ)) ^ 2)⁻¹) ∧
      ∑' j : ℕ, ((1 + h * (j : ℝ)) ^ 2)⁻¹ ≤ 1 + zeta2 / h ^ 2 := by
  have hle : ∀ j : ℕ, ((1 + h * ((j + 1 : ℕ) : ℝ)) ^ 2)⁻¹ ≤ (h ^ 2)⁻¹ * (((j : ℝ) + 1) ^ 2)⁻¹ := by
    intro j
    rw [← mul_inv, ← mul_pow]
    have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have h1 : 0 < h * ((j : ℝ) + 1) := mul_pos hh hj
    apply inv_anti₀ (by positivity)
    push_cast
    nlinarith
  have hsh : Summable (fun j : ℕ => ((1 + h * ((j + 1 : ℕ) : ℝ)) ^ 2)⁻¹) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hle (summable_zeta2.mul_left _)
  have hs : Summable (fun j : ℕ => ((1 + h * (j : ℝ)) ^ 2)⁻¹) := (summable_nat_add_iff 1).1 hsh
  refine ⟨hs, ?_⟩
  rw [hs.tsum_eq_zero_add]
  have h0 : ((1 + h * ((0 : ℕ) : ℝ)) ^ 2)⁻¹ = 1 := by simp
  rw [h0]
  have h2 : ∑' j : ℕ, ((1 + h * ((j + 1 : ℕ) : ℝ)) ^ 2)⁻¹ ≤ (h ^ 2)⁻¹ * zeta2 := by
    rw [zeta2, ← tsum_mul_left]
    exact hsh.tsum_le_tsum hle (summable_zeta2.mul_left _)
  rw [div_eq_inv_mul]
  linarith

theorem cell_bound {h : ℝ} (hh : 0 < h) {x r : ℝ} (hx : |x| ≤ r) :
    ((1 + r) ^ 2)⁻¹ ≤ ((1 + h * ((cellOf h x).2 : ℝ)) ^ 2)⁻¹ := by
  have h1 : ((cellOf h x).2 : ℝ) ≤ |x| / h := Nat.floor_le (div_nonneg (abs_nonneg x) hh.le)
  have h2 : h * ((cellOf h x).2 : ℝ) ≤ |x| := by
    rw [le_div_iff₀ hh] at h1; linarith
  have h3 : (0 : ℝ) ≤ h * ((cellOf h x).2 : ℝ) := by positivity
  apply inv_anti₀ (by positivity)
  have : 1 + h * ((cellOf h x).2 : ℝ) ≤ 1 + r := by linarith
  exact pow_le_pow_left₀ (by linarith) this 2

theorem cell_sep {h : ℝ} (hh : 0 < h) {x x' : ℝ} (hc : cellOf h x = cellOf h x') :
    |x - x'| < h := by
  have hs : decide (x < 0) = decide (x' < 0) := congrArg Prod.fst hc
  have hf : ⌊|x| / h⌋₊ = ⌊|x'| / h⌋₊ := congrArg Prod.snd hc
  have a1 : (⌊|x| / h⌋₊ : ℝ) ≤ |x| / h := Nat.floor_le (div_nonneg (abs_nonneg x) hh.le)
  have a2 : |x| / h < ⌊|x| / h⌋₊ + 1 := Nat.lt_floor_add_one _
  have b1 : (⌊|x'| / h⌋₊ : ℝ) ≤ |x'| / h := Nat.floor_le (div_nonneg (abs_nonneg x') hh.le)
  have b2 : |x'| / h < ⌊|x'| / h⌋₊ + 1 := Nat.lt_floor_add_one _
  rw [hf] at a1 a2
  rw [le_div_iff₀ hh] at a1 b1
  rw [div_lt_iff₀ hh] at a2 b2
  have key : |(|x| - |x'|)| < h := by
    rw [abs_lt]; constructor <;> nlinarith
  by_cases hx : x < 0
  · have hx' : x' < 0 := by simpa [hx] using hs.symm
    rw [abs_of_neg hx, abs_of_neg hx'] at key
    rw [abs_lt] at key ⊢
    constructor <;> linarith [key.1, key.2]
  · have hx' : ¬ x' < 0 := by
      intro h'
      have : decide (x < 0) = true := by rw [hs]; simpa using h'
      exact hx (by simpa using this)
    rw [abs_of_nonneg (not_lt.1 hx), abs_of_nonneg (not_lt.1 hx')] at key
    exact key

/-- **The grid bound.** -/
theorem grid_sum {W : Type*} [Fintype W] [DecidableEq W] {T : Type*} (e : T → W → ℂ) {h : ℝ}
    (hh : 0 < h)
    (hsep : ∀ t t' : T,
      (∀ w, |(e t w).re - (e t' w).re| < h ∧ |(e t w).im - (e t' w).im| < h) → t = t') :
    Summable (fun t : T => ∏ w, ((1 + ‖e t w‖) ^ 4)⁻¹) ∧
      ∑' t : T, ∏ w, ((1 + ‖e t w‖) ^ 4)⁻¹ ≤
        (2 * (1 + zeta2 / h ^ 2)) ^ (Fintype.card W * 2) := by
  obtain ⟨hcs, hct⟩ := summable_cell hh
  set u : Bool × ℕ → ℝ := fun p => ((1 + h * (p.2 : ℝ)) ^ 2)⁻¹ with hu
  have hu0 : ∀ p, 0 ≤ u p := fun p => by positivity
  have hus : Summable u :=
    (summable_prod_of_nonneg hu0).2 ⟨fun _ => hcs, Summable.of_finite⟩
  have hut : ∑' p, u p ≤ 2 * (1 + zeta2 / h ^ 2) := by
    rw [hus.tsum_prod, tsum_fintype, Fintype.sum_bool]
    simp only [hu]
    linarith
  obtain ⟨hGs, hGt⟩ := pi_prod_summable (fun _ : W × Bool => u) (fun _ p => hu0 p) (fun _ => hus)
  set c : T → (W × Bool → Bool × ℕ) := fun t i =>
    cellOf h (if i.2 then (e t i.1).im else (e t i.1).re) with hc
  have hinj : Function.Injective c := by
    intro t t' htt
    refine hsep t t' fun w => ⟨?_, ?_⟩
    · have := congrFun htt (w, false)
      simp only [hc, Bool.false_eq_true, if_false] at this
      exact cell_sep hh this
    · have := congrFun htt (w, true)
      simp only [hc, if_true] at this
      exact cell_sep hh this
  have hle : ∀ t : T, ∏ w, ((1 + ‖e t w‖) ^ 4)⁻¹ ≤ ∏ i : W × Bool, u (c t i) := by
    intro t
    rw [Fintype.prod_prod_type]
    refine Finset.prod_le_prod (fun w _ => by positivity) fun w _ => ?_
    rw [Fintype.prod_bool]
    have h1 : ((1 + ‖e t w‖) ^ 2)⁻¹ ≤ u (c t (w, true)) := by
      simp only [hu, hc, if_true]
      exact cell_bound hh (Complex.abs_im_le_norm _)
    have h2 : ((1 + ‖e t w‖) ^ 2)⁻¹ ≤ u (c t (w, false)) := by
      simp only [hu, hc, Bool.false_eq_true, if_false]
      exact cell_bound hh (Complex.abs_re_le_norm _)
    calc ((1 + ‖e t w‖) ^ 4)⁻¹ = ((1 + ‖e t w‖) ^ 2)⁻¹ * ((1 + ‖e t w‖) ^ 2)⁻¹ := by
          rw [← mul_inv, ← pow_add]
      _ ≤ u (c t (w, true)) * u (c t (w, false)) :=
          mul_le_mul h1 h2 (by positivity) (hu0 _)
  have hcomp : Summable (fun t : T => ∏ i : W × Bool, u (c t i)) := hGs.comp_injective hinj
  have hs : Summable (fun t : T => ∏ w, ((1 + ‖e t w‖) ^ 4)⁻¹) :=
    Summable.of_nonneg_of_le (fun t => Finset.prod_nonneg fun w _ => by positivity) hle hcomp
  refine ⟨hs, ?_⟩
  calc ∑' t : T, ∏ w, ((1 + ‖e t w‖) ^ 4)⁻¹ ≤ ∑' t : T, ∏ i : W × Bool, u (c t i) :=
        hs.tsum_le_tsum hle hcomp
    _ ≤ ∑' a : W × Bool → Bool × ℕ, ∏ i, u (a i) :=
        tsum_comp_le_tsum_of_inj hGs (fun a => Finset.prod_nonneg fun i _ => hu0 _) hinj
    _ ≤ ∏ _i : W × Bool, ∑' p, u p := hGt
    _ = (∑' p, u p) ^ (Fintype.card W * 2) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool]
    _ ≤ (2 * (1 + zeta2 / h ^ 2)) ^ (Fintype.card W * 2) :=
        pow_le_pow_left₀ (tsum_nonneg hu0) hut _

end ArtinKP.H
end

section
-- module Solutions.Artin.KP.H_Sum
attribute [-instance] _root_.ArtinKP.B1.PairClass.instNonempty
/-! # WP-HA, file 2: sums over the nonzero `S`-integers, grouped by their class in `SFin`

* `one_le_prod_mul_norm`: the product formula for `d ∈ R ∖ 0`:
  `∏_w |d|_w · |d|_{S_f} = N(dR) ≥ 1`.
* `sep_class`: two distinct `ν, ν' ∈ R ∖ 0` of the same class `s ∈ SFin` satisfy
  `∏_w |ν − ν'|_w ≥ |s|_{S_f}⁻¹`.
* `fiber_sum`: `∑_{ν ∈ R∖0, [ν] = s} ∏_w (1 + w ν)⁻⁴ ≤ K (1 + |s|_{S_f}^{4r})`, `r = #places`,
  with `K` independent of `s`.
* `summable_class_weight`: `∑_{ν ∈ R∖0} B([ν]) ∏_w (1 + w ν)⁻⁴ < ∞` when `B ≥ 0`,
  `∑_s B(s) < ∞` and `∑_s B(s) |s|^{4r} < ∞`.

No hypothesis on the signature of `F` is used (the count is crude). -/

namespace ArtinKP.H

open NumberField IsDedekindDomain ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-- The product formula on `R ∖ 0`, as an inequality. -/
theorem one_le_prod_mul_norm (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) (d : {ν : SInt 𝔪 // ν ≠ 0}) :
    1 ≤ (∏ w : InfinitePlace F, w ((d : SInt 𝔪) : F) ^ w.mult) *
      (SFin.mk 𝔪 k (Units.mk0 ((d : SInt 𝔪) : F) (H0.coe_ne_zero d))).norm := by
  have hd := H0.coe_ne_zero d
  have h1 := L3X.lnorm_sEmb_gen (k := k) h𝔪 (H0.rowOf h𝔪 g d).1.2 (H0.span_eq_map_rowOf h𝔪 g d)
  have hN : (1 : ℝ) ≤ Ideal.absNorm (H0.rowOf h𝔪 g d).1.1 := by
    have : Ideal.absNorm (H0.rowOf h𝔪 g d).1.1 ≠ 0 := by
      rw [ne_eq, Ideal.absNorm_eq_zero_iff]; exact (H0.rowOf h𝔪 g d).1.2.1
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have hP : 0 < ∏ w : InfinitePlace F, w ((d : SInt 𝔪) : F) ^ w.mult :=
    Finset.prod_pos fun w _ => pow_pos (w.pos_iff.2 hd) _
  have hn := L3X.SFin.norm_mk_pos (k := k) h𝔪 (Units.mk0 _ hd)
  rw [← Real.log_nonneg_iff (mul_pos hP hn), Real.log_mul hP.ne' hn.ne',
    Real.log_prod (fun w _ => (pow_pos (w.pos_iff.2 hd) _).ne')]
  have h2 : L3X.lnorm (sEmb 𝔪 k ((d : SInt 𝔪) : F)) =
      ∑ w : InfinitePlace F, Real.log (w ((d : SInt 𝔪) : F) ^ w.mult) +
        Real.log (SFin.mk 𝔪 k (Units.mk0 ((d : SInt 𝔪) : F) hd)).norm := by
    rw [L3X.lnorm, L3X.sEmb_fin hd]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [L3X.sEmb_fst hd, Real.log_pow]
  rw [← h2, h1]
  exact Real.log_nonneg hN

/-- Two elements of one class of `SFin`: the difference is no larger at `S_f`. -/
theorem norm_mk_sub_le (h𝔪 : 𝔪 ≠ ⊥) {x y : Fˣ} (hxy : SFin.mk 𝔪 k x = SFin.mk 𝔪 k y)
    (hne : (x : F) - (y : F) ≠ 0) :
    (SFin.mk 𝔪 k (Units.mk0 ((x : F) - (y : F)) hne)).norm ≤ (SFin.mk 𝔪 k x).norm := by
  rw [L3X.SFin.norm_mk_eq_prod h𝔪, L3X.SFin.norm_mk_eq_prod h𝔪]
  refine Finset.prod_le_prod (fun v _ => AbsoluteValue.nonneg _ _) fun v hv => ?_
  have hv' : v ∈ placesOf 𝔪 := (L3X.finite_placesOf h𝔪).mem_toFinset.1 hv
  have hmem := (H0.SFin_mk_eq_mk_iff x y).1 hxy v hv'
  have hlt := absNorm_zpow_neg_lt_one v k
  have hx0 : (x : F) ≠ 0 := x.ne_zero
  have e1 : ((x⁻¹ * y : Fˣ) : F) - 1 = (x : F)⁻¹ * (y : F) - 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
  have e2 : (x : F) - (y : F) = -((x : F) * ((x : F)⁻¹ * (y : F) - 1)) := by
    field_simp; ring
  rw [e1] at hmem
  rw [Units.val_mk0, e2, AbsoluteValue.map_neg, map_mul]
  calc NumberField.HeightOneSpectrum.adicAbv F v (x : F) *
        NumberField.HeightOneSpectrum.adicAbv F v ((x : F)⁻¹ * (y : F) - 1)
      ≤ NumberField.HeightOneSpectrum.adicAbv F v (x : F) * 1 :=
        mul_le_mul_of_nonneg_left (hmem.trans hlt.le) (AbsoluteValue.nonneg _ _)
    _ = _ := mul_one _

/-- **Separation inside a class of `SFin`.** -/
theorem sep_class (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) {ν ν' : {ν : SInt 𝔪 // ν ≠ 0}}
    (hs : (sEmb 𝔪 k ((ν : SInt 𝔪) : F)).2.2 = (sEmb 𝔪 k ((ν' : SInt 𝔪) : F)).2.2)
    (hne : ν ≠ ν') :
    ((sEmb 𝔪 k ((ν : SInt 𝔪) : F)).2.2).norm⁻¹ ≤
      ∏ w : InfinitePlace F, w (((ν : SInt 𝔪) : F) - ((ν' : SInt 𝔪) : F)) ^ w.mult := by
  have hν := H0.coe_ne_zero ν
  have hν' := H0.coe_ne_zero ν'
  have hd0 : (ν : SInt 𝔪) - (ν' : SInt 𝔪) ≠ 0 := sub_ne_zero.2 fun h => hne (Subtype.ext h)
  set d : {ν : SInt 𝔪 // ν ≠ 0} := ⟨(ν : SInt 𝔪) - (ν' : SInt 𝔪), hd0⟩ with hd
  have hdF : ((d : SInt 𝔪) : F) = ((ν : SInt 𝔪) : F) - ((ν' : SInt 𝔪) : F) := rfl
  have h1 := one_le_prod_mul_norm (k := k) h𝔪 g d
  rw [L3X.sEmb_fin hν, L3X.sEmb_fin hν'] at hs
  have hne' : ((Units.mk0 _ hν : Fˣ) : F) - ((Units.mk0 _ hν' : Fˣ) : F) ≠ 0 := by
    rw [Units.val_mk0, Units.val_mk0, ← hdF]; exact H0.coe_ne_zero d
  have h2 := norm_mk_sub_le h𝔪 hs hne'
  have hn := L3X.SFin.norm_mk_pos (k := k) h𝔪 (Units.mk0 _ hν)
  have hP : 0 ≤ ∏ w : InfinitePlace F, w ((d : SInt 𝔪) : F) ^ w.mult :=
    Finset.prod_nonneg fun w _ => pow_nonneg (apply_nonneg _ _) _
  rw [L3X.sEmb_fin hν, inv_le_iff_one_le_mul₀ hn, ← hdF]
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ hP)
  exact h2

theorem one_add_pow_le {u : ℝ} (hu : 0 ≤ u) (M : ℕ) : (1 + u) ^ M ≤ 2 ^ M * (1 + u ^ M) := by
  have hM : (0 : ℝ) ≤ u ^ M := pow_nonneg hu M
  have h2 : (0 : ℝ) ≤ 2 ^ M := by positivity
  rcases le_total u 1 with h | h
  · calc (1 + u) ^ M ≤ 2 ^ M := pow_le_pow_left₀ (by linarith) (by linarith) M
      _ ≤ 2 ^ M * (1 + u ^ M) := le_mul_of_one_le_right h2 (by linarith)
  · calc (1 + u) ^ M ≤ (2 * u) ^ M := pow_le_pow_left₀ (by linarith) (by linarith) M
      _ = 2 ^ M * u ^ M := mul_pow _ _ _
      _ ≤ 2 ^ M * (1 + u ^ M) := mul_le_mul_of_nonneg_left (by linarith) h2

/-- **The fibre bound**: the sum over one class of `SFin`, uniformly in the class. -/
theorem fiber_sum (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : SFin 𝔪 k,
      Summable (fun ν : {ν : {ν : SInt 𝔪 // ν ≠ 0} //
          (sEmb 𝔪 k (((ν : SInt 𝔪)) : F)).2.2 = s} =>
        ∏ w : InfinitePlace F, ((1 + w (((ν : {ν : SInt 𝔪 // ν ≠ 0}) : SInt 𝔪) : F)) ^ 4)⁻¹) ∧
      ∑' ν : {ν : {ν : SInt 𝔪 // ν ≠ 0} // (sEmb 𝔪 k (((ν : SInt 𝔪)) : F)).2.2 = s},
        ∏ w : InfinitePlace F, ((1 + w (((ν : {ν : SInt 𝔪 // ν ≠ 0}) : SInt 𝔪) : F)) ^ 4)⁻¹ ≤
          K * (1 + s.norm ^ expo F) := by
  set r := Fintype.card (InfinitePlace F) with hr
  have hz := zeta2_nonneg
  refine ⟨(2 * (1 + 4 * zeta2)) ^ (r * 2) * 2 ^ (r * 4), by positivity, fun s => ?_⟩
  have hn : 0 < s.norm := L3X.SFin.norm_pos h𝔪 s
  set n := s.norm with hndef
  set h : ℝ := min 1 n⁻¹ / 2 with hh
  have hμ : 0 < min 1 n⁻¹ := lt_min one_pos (inv_pos.2 hn)
  have hh0 : 0 < h := by positivity
  have hsep : ∀ ν ν' : {ν : {ν : SInt 𝔪 // ν ≠ 0} // (sEmb 𝔪 k (((ν : SInt 𝔪)) : F)).2.2 = s},
      (∀ w : InfinitePlace F,
        |(w.embedding (((ν : {ν : SInt 𝔪 // ν ≠ 0}) : SInt 𝔪) : F)).re -
            (w.embedding (((ν' : {ν : SInt 𝔪 // ν ≠ 0}) : SInt 𝔪) : F)).re| < h ∧
          |(w.embedding (((ν : {ν : SInt 𝔪 // ν ≠ 0}) : SInt 𝔪) : F)).im -
            (w.embedding (((ν' : {ν : SInt 𝔪 // ν ≠ 0}) : SInt 𝔪) : F)).im| < h) → ν = ν' := by
    intro ν ν' hcell
    by_contra hne
    have hne' : (ν : {ν : SInt 𝔪 // ν ≠ 0}) ≠ ν' := fun h' => hne (Subtype.ext h')
    have hsp := sep_class h𝔪 g (ν.2.trans ν'.2.symm) hne'
    rw [ν.2] at hsp
    set dF : F := (((ν : {ν : SInt 𝔪 // ν ≠ 0}) : SInt 𝔪) : F) -
      (((ν' : {ν : SInt 𝔪 // ν ≠ 0}) : SInt 𝔪) : F) with hdF
    have hw : ∀ w : InfinitePlace F, w dF < min 1 n⁻¹ := by
      intro w
      obtain ⟨c1, c2⟩ := hcell w
      rw [← InfinitePlace.norm_embedding_eq, hdF, map_sub]
      have := Complex.norm_le_abs_re_add_abs_im
        (w.embedding (((ν : {ν : SInt 𝔪 // ν ≠ 0}) : SInt 𝔪) : F) -
          w.embedding (((ν' : {ν : SInt 𝔪 // ν ≠ 0}) : SInt 𝔪) : F))
      rw [Complex.sub_re, Complex.sub_im] at this
      have h2 : h + h = min 1 n⁻¹ := by rw [hh]; ring
      linarith
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
    have hle : ∏ w : InfinitePlace F, w dF ^ w.mult ≤ w₀ dF := by
      calc ∏ w : InfinitePlace F, w dF ^ w.mult
          ≤ ∏ w : InfinitePlace F, (if w = w₀ then w₀ dF else 1) := by
            refine Finset.prod_le_prod (fun w _ => pow_nonneg (apply_nonneg _ _) _) fun w _ => ?_
            have hw1 : w dF ≤ 1 := ((hw w).trans_le (min_le_left _ _)).le
            split_ifs with hw0
            · subst hw0
              exact pow_le_of_le_one (apply_nonneg _ _) hw1 InfinitePlace.mult_pos.ne'
            · exact pow_le_one₀ (apply_nonneg _ _) hw1
        _ = w₀ dF := by simp
    have := (hsp.trans hle).trans_lt ((hw w₀).trans_le (min_le_right _ _))
    exact lt_irrefl _ this
  obtain ⟨hs1, hs2⟩ := grid_sum
    (fun (ν : {ν : {ν : SInt 𝔪 // ν ≠ 0} // (sEmb 𝔪 k (((ν : SInt 𝔪)) : F)).2.2 = s})
      (w : InfinitePlace F) => w.embedding (((ν : {ν : SInt 𝔪 // ν ≠ 0}) : SInt 𝔪) : F)) hh0 hsep
  simp only [InfinitePlace.norm_embedding_eq] at hs1 hs2
  refine ⟨hs1, hs2.trans ?_⟩
  -- the constant
  have hn1 : (0 : ℝ) < 1 + n := by linarith
  have hμ' : (1 + n)⁻¹ ≤ min 1 n⁻¹ :=
    le_min (inv_le_one_of_one_le₀ (by linarith)) (inv_anti₀ hn (by linarith))
  have hh1 : 1 ≤ 2 * (1 + n) * h := by
    have : (1 + n) * (1 + n)⁻¹ = 1 := mul_inv_cancel₀ hn1.ne'
    have h3 : (1 + n) * (1 + n)⁻¹ ≤ (1 + n) * min 1 n⁻¹ := mul_le_mul_of_nonneg_left hμ' hn1.le
    rw [hh]; nlinarith
  have hq : zeta2 / h ^ 2 ≤ zeta2 * (4 * (1 + n) ^ 2) := by
    rw [div_le_iff₀ (by positivity)]
    have : 1 ≤ (2 * (1 + n) * h) ^ 2 := one_le_pow₀ hh1
    nlinarith
  have hA : 2 * (1 + zeta2 / h ^ 2) ≤ 2 * (1 + 4 * zeta2) * (1 + n) ^ 2 := by
    have : (1 : ℝ) ≤ (1 + n) ^ 2 := one_le_pow₀ (by linarith)
    nlinarith
  have hq0 : 0 ≤ zeta2 / h ^ 2 := by positivity
  calc (2 * (1 + zeta2 / h ^ 2)) ^ (r * 2)
      ≤ (2 * (1 + 4 * zeta2) * (1 + n) ^ 2) ^ (r * 2) :=
        pow_le_pow_left₀ (by positivity) hA _
    _ = (2 * (1 + 4 * zeta2)) ^ (r * 2) * (1 + n) ^ (r * 4) := by
        rw [mul_pow, ← pow_mul]; congr 2; ring
    _ ≤ (2 * (1 + 4 * zeta2)) ^ (r * 2) * (2 ^ (r * 4) * (1 + n ^ (r * 4))) :=
        mul_le_mul_of_nonneg_left (one_add_pow_le hn.le _) (by positivity)
    _ = (2 * (1 + 4 * zeta2)) ^ (r * 2) * 2 ^ (r * 4) * (1 + n ^ expo F) := by
        rw [expo]; ring

/-- **Class-weighted sums over `R ∖ 0`.** -/
theorem summable_class_weight (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) (B : SFin 𝔪 k → ℝ)
    (hB0 : ∀ s, 0 ≤ B s) (hB : Summable B) (hB' : Summable fun s => B s * s.norm ^ expo F) :
    Summable (fun ν : {ν : SInt 𝔪 // ν ≠ 0} =>
      B (sEmb 𝔪 k ((ν : SInt 𝔪) : F)).2.2 *
        ∏ w : InfinitePlace F, ((1 + w ((ν : SInt 𝔪) : F)) ^ 4)⁻¹) := by
  obtain ⟨K, hK0, hK⟩ := fiber_sum (k := k) h𝔪 g
  set c : {ν : SInt 𝔪 // ν ≠ 0} → SFin 𝔪 k := fun ν => (sEmb 𝔪 k ((ν : SInt 𝔪) : F)).2.2 with hc
  set f : {ν : SInt 𝔪 // ν ≠ 0} → ℝ := fun ν =>
    B (c ν) * ∏ w : InfinitePlace F, ((1 + w ((ν : SInt 𝔪) : F)) ^ 4)⁻¹ with hf
  have hf0 : ∀ ν, 0 ≤ f ν := fun ν =>
    mul_nonneg (hB0 _) (Finset.prod_nonneg fun w _ => by positivity)
  change Summable f
  rw [← (Equiv.sigmaFiberEquiv c).summable_iff]
  refine (summable_sigma_of_nonneg fun x => hf0 _).2 ⟨fun s => ?_, ?_⟩
  · have := (hK s).1.mul_left (B s)
    refine this.congr fun ν => ?_
    simp only [Equiv.sigmaFiberEquiv_apply, hf]
    rw [show c (ν : {ν : SInt 𝔪 // ν ≠ 0}) = s from ν.2]
  · have hfib : ∀ s : SFin 𝔪 k,
        ∑' ν : {ν : {ν : SInt 𝔪 // ν ≠ 0} // c ν = s}, (f ∘ Equiv.sigmaFiberEquiv c) ⟨s, ν⟩ =
          B s * ∑' ν : {ν : {ν : SInt 𝔪 // ν ≠ 0} // c ν = s},
            ∏ w : InfinitePlace F,
              ((1 + w (((ν : {ν : SInt 𝔪 // ν ≠ 0}) : SInt 𝔪) : F)) ^ 4)⁻¹ := by
      intro s
      rw [← tsum_mul_left]
      refine tsum_congr fun ν => ?_
      simp only [Function.comp_apply, Equiv.sigmaFiberEquiv_apply, hf]
      rw [show c (ν : {ν : SInt 𝔪 // ν ≠ 0}) = s from ν.2]
    refine Summable.of_nonneg_of_le (fun s => tsum_nonneg fun ν => hf0 _) (fun s => ?_)
      ((hB.mul_left K).add (hB'.mul_left K))
    refine (hfib s).le.trans ?_
    calc B s * ∑' ν : {ν : {ν : SInt 𝔪 // ν ≠ 0} // c ν = s},
          ∏ w : InfinitePlace F, ((1 + w (((ν : {ν : SInt 𝔪 // ν ≠ 0}) : SInt 𝔪) : F)) ^ 4)⁻¹
        ≤ B s * (K * (1 + s.norm ^ expo F)) := mul_le_mul_of_nonneg_left (hK s).2 (hB0 s)
      _ = K * B s + K * (B s * s.norm ^ expo F) := by ring

end

end ArtinKP.H
end

section
-- module Solutions.Artin.KP.G2a_Major
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex
/-! # WP-G2a, file 2: the summable majorant of `τ_Φ(ν)·W_{4/3}(ν; v)`

* `ThmE hG hz6 g`: **named hypothesis**, Theorem E for the instance `T.theta hG hz6` in the form
  of `H.tau_eq_coefF'` (`thmE_of_PER` derives it from cube periodicity at every exterior prime
  plus the standing data of `H_Tau`).
* `absNorm_rowOf`: the product formula, exact: `N(νR) = ∏_w |ν|_w^{mult} · |ν|_{S_f}`.
* `norm_tau_le`: `|τ_Φ(ν)| ≤ ∏_w |ν|_w^{2/3} · bf([ν])` with `bf` summable against `|y|^σ`,
  `σ > −1/3` (G1's majorant of the Kirillov function).
* `exists_major`: for every box `vBox F n₀` and every `p` a summable `u` with
  `∏_w (1+|ν|_w)^p · |τ_Φ(ν) W_{4/3}(ν; v)| ≤ u ν` for all `v` in the box.
-/

open scoped ComplexConjugate Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

variable [IsTotallyComplex F]

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (g : AllowedGen ι 𝔪)

variable {hG hz6 g}

/-- **The majorant.** -/
theorem exists_major_oai (hE : ThmE hG hz6 g P) (Φ : GSection ι P 𝔪) (p n₀ : ℕ) :
    ∃ u : {ν : SInt 𝔪 // ν ≠ 0} → ℝ, Summable u ∧ (∀ ν, 0 ≤ u ν) ∧
      ∀ ν : {ν : SInt 𝔪 // ν ≠ 0}, ∀ v ∈ vBox F n₀,
        (∏ w : InfinitePlace F, (1 + w ((ν : SInt 𝔪) : F)) ^ p) *
          ‖T.tau hG hz6 Φ (ν : SInt 𝔪) * Winf (4 / 3) ((ν : SInt 𝔪) : F) v‖ ≤ u ν := by
  obtain ⟨bf, hbf0, hbfs, hbf⟩ := norm_tau_le hE Φ
  obtain ⟨K, hK, hW⟩ := Winf_bound (F := F) p n₀
  have hB : Summable bf := by
    have := hbfs 0 (by norm_num)
    simpa using this
  have hB' : Summable fun s : SFin 𝔪 0 => bf s * s.norm ^ H.expo F := by
    have := hbfs (H.expo F : ℝ) (by
      have : (0 : ℝ) ≤ (H.expo F : ℝ) := Nat.cast_nonneg _
      linarith)
    simpa [Real.rpow_natCast] using this
  have hs := H.summable_class_weight (k := 0) hG.ne_bot g bf hbf0 hB hB'
  refine ⟨fun ν => K * (bf (sEmb 𝔪 0 ((ν : SInt 𝔪) : F)).2.2 *
      ∏ w : InfinitePlace F, ((1 + w ((ν : SInt 𝔪) : F)) ^ 4)⁻¹), hs.mul_left K,
    fun ν => mul_nonneg hK (mul_nonneg (hbf0 _) (Finset.prod_nonneg fun w _ => by positivity)),
    fun ν v hv => ?_⟩
  have h1 := hW ((ν : SInt 𝔪) : F) (H0.coe_ne_zero ν) v hv
  rw [Finset.prod_mul_distrib] at h1
  have hp : 0 ≤ ∏ w : InfinitePlace F, (1 + w ((ν : SInt 𝔪) : F)) ^ p :=
    Finset.prod_nonneg fun w _ => by positivity
  rw [norm_mul]
  calc (∏ w : InfinitePlace F, (1 + w ((ν : SInt 𝔪) : F)) ^ p) *
        (‖T.tau hG hz6 Φ (ν : SInt 𝔪)‖ * ‖Winf (4 / 3) ((ν : SInt 𝔪) : F) v‖)
      ≤ (∏ w : InfinitePlace F, (1 + w ((ν : SInt 𝔪) : F)) ^ p) *
        (((∏ w : InfinitePlace F, w ((ν : SInt 𝔪) : F) ^ (2 / 3 : ℝ)) *
          bf (sEmb 𝔪 0 ((ν : SInt 𝔪) : F)).2.2) * ‖Winf (4 / 3) ((ν : SInt 𝔪) : F) v‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hbf ν) (norm_nonneg _)) hp
    _ = bf (sEmb 𝔪 0 ((ν : SInt 𝔪) : F)).2.2 *
        ((∏ w : InfinitePlace F, w ((ν : SInt 𝔪) : F) ^ (2 / 3 : ℝ)) *
          (∏ w : InfinitePlace F, (1 + w ((ν : SInt 𝔪) : F)) ^ p) *
          ‖Winf (4 / 3) ((ν : SInt 𝔪) : F) v‖) := by ring
    _ ≤ bf (sEmb 𝔪 0 ((ν : SInt 𝔪) : F)).2.2 *
        (K * ∏ w : InfinitePlace F, ((1 + w ((ν : SInt 𝔪) : F)) ^ 4)⁻¹) :=
        mul_le_mul_of_nonneg_left h1 (hbf0 _)
    _ = _ := by ring

end

end ArtinKP.G2a
end

theorem solution.{u_1} : type_of% @ArtinKP.G2a.exists_major_oai.{u_1} := @ArtinKP.G2a.exists_major_oai.{u_1}
