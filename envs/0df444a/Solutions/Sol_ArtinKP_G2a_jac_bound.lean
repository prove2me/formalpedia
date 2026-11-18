-- Prove2me | solution 1 for ArtinKP.G2a.jac_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:01:03.701212+00:00
-- url     : https://prove2.me/submissions/3a0f962b-a6c1-4e66-af9a-a9417d5bee37

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
theorem jac_bound_oai (p n₀ : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ ν : ℂ, ν ≠ 0 → ∀ v : ℝ,
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

end

end ArtinKP.G2a
end

theorem solution : type_of% @ArtinKP.G2a.jac_bound_oai := @ArtinKP.G2a.jac_bound_oai
