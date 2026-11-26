-- Prove2me | solution 1 for Arxivcond_mat_0408414.mean_drc_levy_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T09:21:42.698016+00:00
-- url     : https://prove2.me/submissions/6c224afb-57d6-4905-9739-f6e5626ae0ea

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

lemma J_scale (H s A : ℝ) (hH : 0 < H) (hA : 0 < A) :
    J H s A = ((A ^ (-(1 / (2 * H))) : ℝ) : ℂ) * J H (s * A ^ (-(1 / (2 * H)))) 1 := by
  set b := A ^ (-(1 / (2 * H))) with hb
  have hbp : 0 < b := by positivity
  have := Measure.integral_comp_mul_left (fun k : ℝ => Complex.exp ((((s * b) * k : ℝ) : ℂ) * Complex.I) *
      ((Real.exp (-1 * |k| ^ (2 * H)) : ℝ) : ℂ)) b⁻¹
  rw [inv_inv, abs_of_pos hbp] at this
  unfold J
  rw [← Complex.real_smul, ← this]
  congr 1; ext u
  congr 3
  · field_simp
  · rw [abs_mul, abs_inv, abs_of_pos hbp, mul_rpow (by positivity) (abs_nonneg _), hb, ← rpow_neg hA.le,
      ← rpow_mul hA.le]
    rw [neg_neg, show (1 / (2 * H) * (2 * H)) = 1 by field_simp, rpow_one]; ring

lemma J_one (H x : ℝ) : J H x 1 = ((2 * π * levyDensity (2 * H) x : ℝ) : ℂ) := by
  have hJ : J H x 1 = ((J H x 1).re : ℂ) := (Complex.conj_eq_iff_re.mp (J_real H x 1)).symm
  rw [hJ]; congr 1
  unfold levyDensity
  rw [mul_div_cancel₀ _ (by positivity)]
  unfold J
  congr 2; ext k
  congr 3
  · ring
  · ring

end DR2

open Arxivcond_mat_0408414 DR2 in
theorem solution (lam s H θ θ0 : ℝ) (hlam : 0 < lam) (hs : 0 < s)
    (hH0 : 0 < H) (hH1 : H ≤ 1)
    (hθ : θ ∈ Set.Ioo (-(π / 2)) (π / 2)) (hθ0 : θ0 ∈ Set.Ioo (-(π / 2)) (π / 2)) :
    (∀ v : ℝ, gaussOmega lam s H θ θ0 v =
      ((Real.exp (-((2 * π / lam) * (cos θ + cos θ0) / √2 * s * lam ^ (1 - H) * |v| ^ H) ^ 2) : ℝ) : ℂ)) ∧
    Tendsto (fun L : ℝ => kirchhoffMDRC lam θ θ0 L (gaussOmega lam s H θ θ0)) atTop
      (𝓝 ((mdrcFinal H s θ θ0 : ℝ) : ℂ)) := by
  have h2 : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
  have h2p : 0 < √2 := by positivity
  refine ⟨fun v => ?_, ?_⟩
  · rw [gauss_eq]; unfold incStd
    congr 3
    rw [div_rpow (abs_nonneg _) hlam.le]
    have : lam ^ (1 - H) = lam / lam ^ H := by rw [rpow_sub hlam, rpow_one]
    rw [this]
    have : 0 < lam ^ H := by positivity
    field_simp
    rw [h2]; ring
  have hc : 0 < cos θ + cos θ0 := by
    have := cos_pos_of_mem_Ioo hθ; have := cos_pos_of_mem_Ioo hθ0; linarith
  set A := (2 * π * (cos θ + cos θ0) * s) ^ 2 / 2 with hA
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
      gaussOmega lam s H θ θ0 v = g (lam⁻¹ * v) := by
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
  have hlim : Tendsto (fun L : ℝ => kirchhoffMDRC lam θ θ0 L (gaussOmega lam s H θ θ0)) atTop
      (𝓝 (((2 * π / lam / (2 * π) * (1 / cos θ0) * (cos ((θ + θ0) / 2) / cos ((θ - θ0) / 2)) ^ 2 : ℝ) : ℂ) *
        ∫ v, g (lam⁻¹ * v))) := by
    unfold kirchhoffMDRC
    simp_rw [hfeq]
    refine tendsto_const_nhds.mul (intervalIntegral_tendsto_integral hfi ?_ ?_)
    · exact tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const two_pos)
    · exact tendsto_id.atTop_div_const two_pos
  have hAp : 0 < A := by positivity
  convert hlim using 2
  rw [hsub, J_scale _ _ _ hH0 hAp, J_one]
  simp only [← Complex.ofReal_mul]
  congr 1
  unfold mdrcFinal levyPrefactor levyArg
  rw [tan_eq_sin_div_cos]
  have hcp : 0 < cos ((θ + θ0) / 2) := cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, hθ0.1], by linarith [hθ.2, hθ0.2]⟩
  have hcm : 0 < cos ((θ - θ0) / 2) := cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, hθ0.2], by linarith [hθ.2, hθ0.1]⟩
  have hc0 : 0 < cos θ0 := cos_pos_of_mem_Ioo hθ0
  set cp := cos ((θ + θ0) / 2)
  set cm := cos ((θ - θ0) / 2)
  have hcsum : cos θ + cos θ0 = 2 * cp * cm := by rw [Real.cos_add_cos]
  have hssub : sin θ - sin θ0 = 2 * sin ((θ - θ0) / 2) * cp := by rw [Real.sin_sub_sin]
  set sm := sin ((θ - θ0) / 2)
  have hlA0 : levyA θ θ0 = 2 * π * √2 * cp * cm := by unfold levyA; rfl
  clear_value cp cm sm
  set a := 2 * π * √2 * cp * cm with ha
  have hap : 0 < a := by positivity
  have hA2 : A = (a * s) ^ 2 := by
    rw [hA, hcsum, ha]; simp only [mul_pow, h2]; ring
  have hbq : A ^ (-(1 / (2 * H))) = a⁻¹ * a ^ (-(1 / H - 1)) * s ^ (-(1 / H)) := by
    rw [hA2, ← rpow_natCast, ← rpow_mul (by positivity), mul_rpow hap.le hs.le, ← rpow_neg_one,
      ← rpow_add hap]
    congr 2
    all_goals (push_cast; field_simp)
    all_goals ring
  have hE' : a ^ (1 / H - 1) = (a ^ (-(1 / H - 1)))⁻¹ := by rw [rpow_neg hap.le, inv_inv]
  have hS' : s ^ (1 / H) = (s ^ (-(1 / H)))⁻¹ := by rw [rpow_neg hs.le, inv_inv]
  have hEp : 0 < a ^ (-(1 / H - 1)) := by positivity
  have hSp : 0 < s ^ (-(1 / H)) := by positivity
  rw [hlA0]
  rw [hE', hS', hbq, hssub]
  generalize a ^ (-(1 / H - 1)) = E at hEp ⊢
  generalize s ^ (-(1 / H)) = Sg at hSp ⊢
  have harg : √2 * (sm / cm) / (E⁻¹ * Sg⁻¹) = 2 * π * (2 * sm * cp) * (a⁻¹ * E * Sg) := by
    rw [ha]; field_simp; rw [h2]; ring
  rw [harg]
  rw [ha]; field_simp
