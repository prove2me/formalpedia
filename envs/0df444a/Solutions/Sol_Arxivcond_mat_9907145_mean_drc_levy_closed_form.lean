-- Prove2me | solution 1 for Arxivcond_mat_9907145.mean_drc_levy_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T09:19:17.359652+00:00
-- url     : https://prove2.me/submissions/0f958439-ddb9-4e69-bf69-ce6649b415c4

import Mathlib
import Definitions.Def_Arxivcond_mat_9907145_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real
noncomputable section
namespace LV
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

end LV

open Arxivcond_mat_9907145 LV in
theorem solution (lam ell H θ θ0 : ℝ) (hlam : 0 < lam) (hell : 0 < ell)
    (hH0 : 0 < H) (hH1 : H ≤ 1)
    (hθ : θ ∈ Set.Ioo (-(π / 2)) (π / 2)) (hθ0 : θ0 ∈ Set.Ioo (-(π / 2)) (π / 2)) :
    (∀ v : ℝ, gaussOmega (2 * π / lam) ell H θ θ0 v =
      ((Real.exp (-((2 * π / lam) * ((cos θ + cos θ0) / √2) * ell ^ (1 - H) * |v| ^ H) ^ 2) : ℝ) : ℂ)) ∧
    Tendsto (fun L : ℝ => kirchhoffMDRC (2 * π / lam) θ θ0 L (gaussOmega (2 * π / lam) ell H θ θ0))
      atTop (𝓝 ((mdrcFinal H (ell / lam) θ θ0 : ℝ) : ℂ)) := by
  have h2 : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
  have h2p : 0 < √2 := by positivity
  refine ⟨fun v => ?_, ?_⟩
  · rw [gauss_eq]; unfold incStd
    congr 3
    rw [show (2 * π / lam * ((cos θ + cos θ0) / √2) * ell ^ (1 - H) * |v| ^ H) ^ 2 =
      (2 * π / lam * (cos θ + cos θ0)) ^ 2 * (ell ^ (1 - H) * |v| ^ H) ^ 2 / √2 ^ 2 by ring, h2]
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
  have hAp : 0 < A := by rw [hA]; positivity
  convert hlim using 2
  rw [hsub, J_scale _ _ _ hH0 hAp, J_one]
  simp only [← Complex.ofReal_mul]
  congr 1
  unfold mdrcFinal
  rw [tan_eq_sin_div_cos]
  have hcp : 0 < cos ((θ + θ0) / 2) := cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, hθ0.1], by linarith [hθ.2, hθ0.2]⟩
  have hcm : 0 < cos ((θ - θ0) / 2) := cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, hθ0.2], by linarith [hθ.2, hθ0.1]⟩
  have hc0 : 0 < cos θ0 := cos_pos_of_mem_Ioo hθ0
  set cp := cos ((θ + θ0) / 2)
  set cm := cos ((θ - θ0) / 2)
  have hcsum : cos θ + cos θ0 = 2 * cp * cm := by rw [Real.cos_add_cos]
  have hssub : sin θ - sin θ0 = 2 * sin ((θ - θ0) / 2) * cp := by rw [Real.sin_sub_sin]
  set sm := sin ((θ - θ0) / 2)
  have hlA0 : levyA (ell / lam) θ θ0 = √2 * (2 * π * (ell / lam)) * cp * cm := by unfold levyA; rfl
  clear_value cp cm sm
  set p := √2 * cp * cm with hp
  have hpp : 0 < p := by positivity
  set t := 2 * π * (ell / lam) with ht
  have htp : 0 < t := by positivity
  have hA2 : A = p ^ 2 * t ^ (2 - 2 * H) := by
    have h3 : ((ell / lam) ^ (1 - H)) ^ 2 = (ell / lam) ^ (2 - 2 * H) := by
      rw [← rpow_natCast, ← rpow_mul (by positivity)]; norm_num; ring_nf
    rw [hAeq, h3, hcsum, mul_assoc ((2 * cp * cm) ^ 2), ← mul_rpow (by positivity) (by positivity), ← ht, hp]
    simp only [mul_pow, h2]; ring
  have hbq : A ^ (-(1 / (2 * H))) = p⁻¹ * (p * t) ^ (-(1 / H - 1)) := by
    rw [hA2, mul_rpow (by positivity) (by positivity), mul_rpow hpp.le htp.le, ← rpow_natCast,
      ← rpow_mul hpp.le, ← rpow_mul htp.le, ← rpow_neg_one, ← mul_assoc, ← rpow_add hpp]
    congr 2
    all_goals (push_cast; field_simp)
    all_goals ring
  have hlA : levyA (ell / lam) θ θ0 = p * t := by rw [hlA0, hp, ht]; ring
  rw [hlA, hbq, hssub]
  set E := (p * t) ^ (-(1 / H - 1)) with hE
  have hEp : 0 < E := by positivity
  have hE' : (p * t) ^ (1 / H - 1) = E⁻¹ := by rw [hE, rpow_neg (by positivity), inv_inv]
  rw [hE']
  have harg : √2 * (sm / cm) / E⁻¹ = 2 * sm * cp * (p⁻¹ * E) := by
    rw [hp]; field_simp; rw [h2]; ring
  rw [harg]
  rw [hK]; field_simp
  rw [hp]
