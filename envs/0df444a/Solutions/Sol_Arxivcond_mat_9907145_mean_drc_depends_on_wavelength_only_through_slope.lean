-- Prove2me | solution 1 for Arxivcond_mat_9907145.mean_drc_depends_on_wavelength_only_through_slope
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T09:11:14.20193+00:00
-- url     : https://prove2.me/submissions/c501b4d5-24f0-4fe9-9e26-a303eca22850

import Mathlib
import Definitions.Def_Arxivcond_mat_9907145_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real
noncomputable section
namespace DR
open Arxivcond_mat_9907145

lemma integ_g (b p : ℝ) (hb : 0 < b) (hp : 0 < p) :
    Integrable (fun x : ℝ => Real.exp (-b * |x| ^ p)) := by
  have h1 : IntegrableOn (fun x : ℝ => Real.exp (-b * |x| ^ p)) (Set.Ioi 0) := by
    refine (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 0) (by norm_num) hp hb).congr_fun
      (fun x hx => ?_) measurableSet_Ioi
    simp [abs_of_pos (Set.mem_Ioi.mp hx)]
  rw [← integrableOn_univ, ← @Set.Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, h1⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
  simp only [Function.comp_def, Set.neg_preimage, Set.neg_Iio, neg_zero, abs_neg]
  exact h1

/-- the real-valued integral -/
def J (H s A : ℝ) : ℂ := ∫ u : ℝ, Complex.exp (((s * u : ℝ) : ℂ) * Complex.I) *
  ((Real.exp (-A * |u| ^ (2 * H)) : ℝ) : ℂ)

lemma J_real (H s A : ℝ) : (starRingEnd ℂ) (J H s A) = J H s A := by
  unfold J
  rw [← integral_conj]
  rw [← integral_neg_eq_self]
  congr 1; ext u
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_I, abs_neg]
  congr 2
  push_cast; ring

lemma gauss_eq (K ell H θ θ0 v : ℝ) :
    gaussOmega K ell H θ θ0 v =
      ((Real.exp (-((K * (cos θ + cos θ0)) ^ 2 * (incStd ell H |v|) ^ 2 / 2)) : ℝ) : ℂ) := by
  unfold gaussOmega
  have := charFun_gaussianReal (μ := 0) (v := ⟨(incStd ell H |v|) ^ 2, sq_nonneg _⟩)
    (-(K * (cos θ + cos θ0)))
  rw [charFun_apply_real] at this
  convert this using 1
  · congr 1; ext z; congr 1; push_cast; ring
  · have e : ((⟨(incStd ell H |v|) ^ 2, sq_nonneg _⟩ : NNReal) : ℝ) = (incStd ell H |v|) ^ 2 := rfl
    change _ = Complex.exp (_ - ((incStd ell H |v| ^ 2 : ℝ) : ℂ) * _ / 2)
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring

lemma inc_sq (ell H v : ℝ) (he : 0 < ell) : (incStd ell H |v|) ^ 2 = ell ^ (2 - 2 * H) * |v| ^ (2 * H) := by
  unfold incStd
  rw [mul_pow, ← rpow_natCast, ← rpow_natCast (|v| ^ H), ← rpow_mul he.le, ← rpow_mul (abs_nonneg v)]
  norm_num; ring_nf

end DR

open Arxivcond_mat_9907145 DR in
theorem solution (H : ℝ) (hH0 : 0 < H) (hH1 : H ≤ 1) :
    ∃ F : ℝ → ℝ → ℝ → ℝ, ∀ lam ell θ θ0 : ℝ, 0 < lam → 0 < ell →
      θ ∈ Set.Ioo (-(π / 2)) (π / 2) → θ0 ∈ Set.Ioo (-(π / 2)) (π / 2) →
      Tendsto (fun L : ℝ => kirchhoffMDRC (2 * π / lam) θ θ0 L (gaussOmega (2 * π / lam) ell H θ θ0))
        atTop (𝓝 ((F ((ell / lam) ^ (1 - H)) θ θ0 : ℝ) : ℂ)) := by
  refine ⟨fun ρ θ θ0 => (((1 / (2 * π) * (1 / cos θ0) * (cos ((θ + θ0) / 2) ^ 2 / cos ((θ - θ0) / 2) ^ 2) : ℝ) : ℂ) *
      J H (sin θ - sin θ0) ((cos θ + cos θ0) ^ 2 * (2 * π) ^ (2 - 2 * H) * ρ ^ 2 / 2)).re, ?_⟩
  intro lam ell θ θ0 hlam hell hθ hθ0
  set K := 2 * π / lam with hK
  have hKp : 0 < K := by positivity
  have hc : 0 < cos θ + cos θ0 := by
    have := cos_pos_of_mem_Ioo hθ; have := cos_pos_of_mem_Ioo hθ0; linarith
  set B := (K * (cos θ + cos θ0)) ^ 2 * ell ^ (2 - 2 * H) / 2 with hB
  have hBp : 0 < B := by positivity
  set f : ℝ → ℂ := fun v => Complex.exp (((K * (sin θ - sin θ0) * v : ℝ) : ℂ) * Complex.I) * ((Real.exp (-B * |v| ^ (2 * H)) : ℝ) : ℂ) with hf
  have hfeq : ∀ v, Complex.exp (((K * (sin θ - sin θ0) * v : ℝ) : ℂ) * Complex.I) * gaussOmega K ell H θ θ0 v = f v := by
    intro v
    rw [gauss_eq, inc_sq _ _ _ hell]
    simp only [hf, hB]; congr 3; ring
  have hfi : Integrable f := by
    refine Integrable.mono' (integ_g B (2 * H) hBp (by linarith)) ?_ (Eventually.of_forall fun v => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      simp only [hf]
      refine Continuous.mul (by fun_prop) (Complex.continuous_ofReal.comp ?_)
      exact Real.continuous_exp.comp (continuous_const.mul ((continuous_abs).rpow_const (fun _ => Or.inr (by linarith))))
    · simp only [hf, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), le_refl]
  set A := B * K ^ (-(2 * H)) with hA
  have hsub : ∫ v, f v = ((K⁻¹ : ℝ) : ℂ) * J H (sin θ - sin θ0) A := by
    have := Measure.integral_comp_mul_left (fun u : ℝ => Complex.exp ((((sin θ - sin θ0) * u : ℝ) : ℂ) * Complex.I) *
      ((Real.exp (-A * |u| ^ (2 * H)) : ℝ) : ℂ)) K
    rw [abs_of_pos (inv_pos.mpr hKp)] at this
    unfold J
    rw [← Complex.real_smul, ← this]
    congr 1; ext v
    simp only [hf, hA]
    congr 3
    · ring
    · rw [abs_mul, abs_of_pos hKp, mul_rpow hKp.le (abs_nonneg v)]
      have : K ^ (-(2 * H)) * K ^ (2 * H) = 1 := by rw [← rpow_add hKp]; simp
      calc -B * |v| ^ (2 * H) = -B * (K ^ (-(2 * H)) * K ^ (2 * H)) * |v| ^ (2 * H) := by rw [this]; ring
        _ = _ := by ring
  have hAeq : A = (cos θ + cos θ0) ^ 2 * (2 * π) ^ (2 - 2 * H) * ((ell / lam) ^ (1 - H)) ^ 2 / 2 := by
    have h1 : K * ell = 2 * π * (ell / lam) := by rw [hK]; field_simp
    have h2 : K ^ 2 * K ^ (-(2 * H)) * ell ^ (2 - 2 * H) = (K * ell) ^ (2 - 2 * H) := by
      rw [mul_rpow hKp.le hell.le, ← rpow_natCast, ← rpow_add hKp]; norm_num; ring_nf; simp
    have h3 : ((ell / lam) ^ (1 - H)) ^ 2 = (ell / lam) ^ (2 - 2 * H) := by
      rw [← rpow_natCast, ← rpow_mul (by positivity)]; norm_num; ring_nf
    rw [h3, mul_assoc ((cos θ + cos θ0) ^ 2), ← mul_rpow (by positivity) (by positivity), ← h1, ← h2, hA, hB]; ring
  have hlim : Tendsto (fun L : ℝ => kirchhoffMDRC K θ θ0 L (gaussOmega K ell H θ θ0)) atTop
      (𝓝 (((K / (2 * π) * (1 / cos θ0) * (cos ((θ + θ0) / 2) ^ 2 / cos ((θ - θ0) / 2) ^ 2) : ℝ) : ℂ) * ∫ v, f v)) := by
    unfold kirchhoffMDRC
    simp_rw [hfeq]
    refine tendsto_const_nhds.mul (intervalIntegral_tendsto_integral hfi ?_ ?_)
    · exact tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const two_pos)
    · exact tendsto_id.atTop_div_const two_pos
  convert hlim using 2
  dsimp only
  rw [hsub, ← hAeq]
  have hJ : J H (sin θ - sin θ0) A = ((J H (sin θ - sin θ0) A).re : ℂ) := by
    have := J_real H (sin θ - sin θ0) A
    exact (Complex.conj_eq_iff_re.mp this).symm
  rw [hJ, ← Complex.ofReal_mul, Complex.ofReal_re, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  field_simp

