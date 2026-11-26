-- Prove2me | solution 1 for Arxivcond_mat_0408414.mean_drc_depends_on_wavelength_only_through_slope
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T09:13:47.588247+00:00
-- url     : https://prove2.me/submissions/db11fdcf-6c01-4ba3-81ab-b1b76ff13ca0

import Mathlib
import Definitions.Def_Arxivcond_mat_0408414_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real Asymptotics
noncomputable section
namespace DR2
open Arxivcond_mat_0408414

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

lemma gauss_eq (lam sl H θ θ0 v : ℝ) :
    gaussOmega lam sl H θ θ0 v =
      ((Real.exp (-((2 * π / lam * (cos θ + cos θ0)) ^ 2 * (incStd lam sl H |v|) ^ 2 / 2)) : ℝ) : ℂ) := by
  unfold gaussOmega
  have := charFun_gaussianReal (μ := 0) (v := ⟨(incStd lam sl H |v|) ^ 2, sq_nonneg _⟩)
    (-(2 * π / lam * (cos θ + cos θ0)))
  rw [charFun_apply_real] at this
  convert this using 1
  · congr 1; ext z; congr 1; push_cast; ring
  · change _ = Complex.exp (_ - ((incStd lam sl H |v| ^ 2 : ℝ) : ℂ) * _ / 2)
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring

end DR2

open Arxivcond_mat_0408414 DR2 in
theorem solution (H : ℝ) (hH0 : 0 < H) (hH1 : H ≤ 1) :
    ∃ F : ℝ → ℝ → ℝ → ℝ, ∀ lam ell θ θ0 : ℝ, 0 < lam → 0 < ell →
      θ ∈ Set.Ioo (-(π / 2)) (π / 2) → θ0 ∈ Set.Ioo (-(π / 2)) (π / 2) →
      Tendsto (fun L : ℝ => kirchhoffMDRC lam θ θ0 L (gaussOmega lam (Arxivcond_mat_0408414.slope ell H lam) H θ θ0))
        atTop (𝓝 ((F (Arxivcond_mat_0408414.slope ell H lam) θ θ0 : ℝ) : ℂ)) := by
  refine ⟨fun ρ θ θ0 => ((((1 / cos θ0) * (cos ((θ + θ0) / 2) / cos ((θ - θ0) / 2)) ^ 2 : ℝ) : ℂ) *
      J H (2 * π * (sin θ - sin θ0)) ((2 * π * (cos θ + cos θ0) * ρ) ^ 2 / 2)).re, ?_⟩
  intro lam ell θ θ0 hlam hell hθ hθ0
  have hc : 0 < cos θ + cos θ0 := by
    have := cos_pos_of_mem_Ioo hθ; have := cos_pos_of_mem_Ioo hθ0; linarith
  have hρ : 0 < Arxivcond_mat_0408414.slope ell H lam := by unfold Arxivcond_mat_0408414.slope; positivity
  set ρ := Arxivcond_mat_0408414.slope ell H lam
  set A := (2 * π * (cos θ + cos θ0) * ρ) ^ 2 / 2 with hA
  have hAp : 0 < A := by positivity
  set g : ℝ → ℂ := fun u => Complex.exp ((((2 * π * (sin θ - sin θ0)) * u : ℝ) : ℂ) * Complex.I) *
    ((Real.exp (-A * |u| ^ (2 * H)) : ℝ) : ℂ) with hg
  have hgi : Integrable g := by
    refine Integrable.mono' (integ_g A (2 * H) hAp (by linarith)) ?_ (Eventually.of_forall fun v => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      simp only [hg]
      refine Continuous.mul (by fun_prop) (Complex.continuous_ofReal.comp ?_)
      exact Real.continuous_exp.comp (continuous_const.mul ((continuous_abs).rpow_const (fun _ => Or.inr (by linarith))))
    · simp only [hg, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), le_refl]
  have hfeq : ∀ v, Complex.exp ((((2 * π / lam) * (sin θ - sin θ0) * v : ℝ) : ℂ) * Complex.I) *
      gaussOmega lam ρ H θ θ0 v = g (lam⁻¹ * v) := by
    intro v
    rw [gauss_eq]
    simp only [hg, hA]
    congr 3
    · field_simp
    · unfold incStd
      rw [abs_mul, abs_inv, abs_of_pos hlam, ← div_eq_inv_mul, mul_comm 2 H, rpow_mul (by positivity), rpow_two]
      field_simp
  have hfi : Integrable (fun v => g (lam⁻¹ * v)) := hgi.comp_mul_left' (inv_ne_zero hlam.ne')
  have hsub : ∫ v, g (lam⁻¹ * v) = ((lam : ℝ) : ℂ) * J H (2 * π * (sin θ - sin θ0)) A := by
    rw [Measure.integral_comp_mul_left g lam⁻¹, inv_inv, abs_of_pos hlam, Complex.real_smul]
    rfl
  have hlim : Tendsto (fun L : ℝ => kirchhoffMDRC lam θ θ0 L (gaussOmega lam ρ H θ θ0)) atTop
      (𝓝 (((2 * π / lam / (2 * π) * (1 / cos θ0) * (cos ((θ + θ0) / 2) / cos ((θ - θ0) / 2)) ^ 2 : ℝ) : ℂ) *
        ∫ v, g (lam⁻¹ * v))) := by
    unfold kirchhoffMDRC
    simp_rw [hfeq]
    refine tendsto_const_nhds.mul (intervalIntegral_tendsto_integral hfi ?_ ?_)
    · exact tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const two_pos)
    · exact tendsto_id.atTop_div_const two_pos
  convert hlim using 2
  dsimp only
  rw [hsub]
  have hJ : J H (2 * π * (sin θ - sin θ0)) A = ((J H (2 * π * (sin θ - sin θ0)) A).re : ℂ) := by
    have := J_real H (2 * π * (sin θ - sin θ0)) A
    exact (Complex.conj_eq_iff_re.mp this).symm
  rw [hJ, ← Complex.ofReal_mul, Complex.ofReal_re, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  field_simp
