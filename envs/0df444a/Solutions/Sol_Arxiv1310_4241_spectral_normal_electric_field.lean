-- Prove2me | solution 1 for Arxiv1310_4241.spectral_normal_electric_field
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T20:18:53.751855+00:00
-- url     : https://prove2.me/submissions/03f50073-daf2-4316-a6ef-3bec7e1922e3

import Mathlib
import Definitions.Def_Arxiv1310_4241_Basic

open MeasureTheory Filter Topology Arxiv1310_4241

/-! ### Part 1: Basic properties of `sommerfeldRoot` -/

private lemma sommerfeldRoot_sq (k : ℂ) (ξ η : ℝ) :
    sommerfeldRoot k ξ η ^ 2 = (ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2 := by
  unfold sommerfeldRoot
  set z : ℂ := (ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2
  split_ifs with h
  · have hz : z = (z.re : ℂ) := by apply Complex.ext <;> simp [h.1]
    have hneg : 0 ≤ -z.re := by linarith [h.2]
    calc (-Complex.I * (Real.sqrt (-z.re) : ℂ)) ^ 2
        = (Complex.I ^ 2) * ((Real.sqrt (-z.re) : ℝ) : ℂ) ^ 2 := by ring
      _ = -1 * ((-z.re : ℝ) : ℂ) := by
          rw [Complex.I_sq]; norm_cast; rw [Real.sq_sqrt hneg]
      _ = (z.re : ℂ) := by push_cast; ring
      _ = z := hz.symm
  · by_cases hz0 : z = 0
    · simp [hz0]
    · rw [sq, ← Complex.cpow_add _ _ hz0]; norm_num

private lemma sommerfeldRoot_re_nonneg (k : ℂ) (ξ η : ℝ) :
    0 ≤ (sommerfeldRoot k ξ η).re := by
  unfold sommerfeldRoot
  set z : ℂ := (ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2
  split_ifs with h
  · simp
  · by_cases hz0 : z = 0
    · simp [hz0]
    · rw [Complex.cpow_def_of_ne_zero hz0, Complex.exp_re]
      apply mul_nonneg (Real.exp_nonneg _)
      have him : (Complex.log z * (1 / 2 : ℂ)).im = z.arg / 2 := by
        simp [Complex.log_im]; ring
      rw [him]
      apply Real.cos_nonneg_of_mem_Icc
      have h1 := Complex.neg_pi_lt_arg z
      have h2 := Complex.arg_le_pi z
      constructor <;> linarith

private lemma sommerfeldRoot_re_sq_ge (k : ℂ) (ξ η : ℝ) :
    ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2).re ≤ (sommerfeldRoot k ξ η).re ^ 2 := by
  have hsq : (sommerfeldRoot k ξ η ^ 2).re = (sommerfeldRoot k ξ η).re ^ 2 - (sommerfeldRoot k ξ η).im ^ 2 := by
    rw [sq, Complex.mul_re]; ring
  rw [sommerfeldRoot_sq] at hsq
  nlinarith [sq_nonneg (sommerfeldRoot k ξ η).im]

private lemma norm_sommerfeldRoot_sq_eq (k : ℂ) (ξ η : ℝ) :
    ‖sommerfeldRoot k ξ η‖ ^ 2 = ‖(ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2‖ := by
  rw [← norm_pow, sommerfeldRoot_sq]

private lemma norm_sommerfeldRoot_le (k : ℂ) (ξ η : ℝ) :
    ‖sommerfeldRoot k ξ η‖ ≤ (1 + ‖k‖) * Real.sqrt (1 + ξ ^ 2 + η ^ 2) := by
  have h1 : ‖sommerfeldRoot k ξ η‖ ^ 2 ≤ ξ ^ 2 + η ^ 2 + ‖k‖ ^ 2 := by
    rw [norm_sommerfeldRoot_sq_eq]
    calc ‖(ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2‖
        ≤ ‖(ξ : ℂ) ^ 2 + (η : ℂ) ^ 2‖ + ‖k ^ 2‖ := norm_sub_le _ _
      _ = ξ ^ 2 + η ^ 2 + ‖k‖ ^ 2 := by
          have : (ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 = ((ξ ^ 2 + η ^ 2 : ℝ) : ℂ) := by push_cast; ring
          rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_pow]
  have h2 : ‖sommerfeldRoot k ξ η‖ ^ 2 ≤ ((1 + ‖k‖) * Real.sqrt (1 + ξ ^ 2 + η ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith [norm_nonneg k, sq_nonneg ξ, sq_nonneg η]
  exact le_of_sq_le_sq h2 (by positivity)

private lemma norm_exp_neg_sommerfeldRoot_le_one (k : ℂ) (ξ η z : ℝ) (hz : 0 ≤ z) :
    ‖Complex.exp (-(sommerfeldRoot k ξ η) * (z : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  apply Real.exp_le_one_iff.mpr
  have hre : (-(sommerfeldRoot k ξ η) * (z : ℂ)).re = -(sommerfeldRoot k ξ η).re * z := by simp
  rw [hre]
  nlinarith [sommerfeldRoot_re_nonneg k ξ η]

private lemma norm_planeWave (ξ η x y : ℝ) : ‖planeWave ξ η x y‖ = 1 := by
  unfold planeWave
  have : Complex.I * ((ξ : ℂ) * (x : ℂ) + (η : ℂ) * (y : ℂ)) =
      (((ξ * x + η * y : ℝ) : ℂ) * Complex.I) := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

private lemma measurable_sommerfeldRoot (k : ℂ) :
    Measurable (fun ζ : ℝ × ℝ => sommerfeldRoot k ζ.1 ζ.2) := by
  unfold sommerfeldRoot
  have hf : Measurable (fun ζ : ℝ × ℝ => (ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - k ^ 2) := by fun_prop
  refine Measurable.ite ?_ ?_ ?_
  · exact (Complex.continuous_im.measurable.comp hf (measurableSet_singleton 0)).inter
      (Complex.continuous_re.measurable.comp hf measurableSet_Iio)
  · exact measurable_const.mul
      (Complex.continuous_ofReal.measurable.comp
        (Real.continuous_sqrt.measurable.comp
          (continuous_neg.measurable.comp (Complex.continuous_re.measurable.comp hf))))
  · have hcpow : (fun ζ : ℝ × ℝ => ((ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - k ^ 2) ^ (1 / 2 : ℂ)) =
        fun ζ => if (ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - k ^ 2 = 0 then 0
          else Complex.exp (Complex.log ((ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - k ^ 2) * (1 / 2 : ℂ)) := by
      ext ζ; rw [Complex.cpow_def]; simp
    rw [hcpow]
    exact Measurable.ite (hf (measurableSet_singleton 0)) measurable_const
      (Complex.continuous_exp.measurable.comp ((Complex.measurable_log.comp hf).mul measurable_const))

private lemma measurable_ghat (k : ℂ) (z : ℝ) :
    Measurable (fun ζ : ℝ × ℝ => ghat k ζ.1 ζ.2 z) := by
  unfold ghat
  have hβ := measurable_sommerfeldRoot k
  exact (Complex.continuous_exp.measurable.comp (hβ.neg.mul measurable_const)).div
    (measurable_const.mul hβ)

/-! ### Part 2: Glaisher / Schwinger 1D integrals -/

private lemma glaisher_core (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ u in Set.Ioi (0 : ℝ), Real.exp (-((a * u - b / (2 * u)) ^ 2))) = Real.sqrt Real.pi / (2 * a) ∧
    IntegrableOn (fun u : ℝ => Real.exp (-((a * u - b / (2 * u)) ^ 2))) (Set.Ioi 0) := by
  let g : ℝ → ℝ := fun u => a * u - b / (2 * u)
  let g' : ℝ → ℝ := fun u => a + b / (2 * u ^ 2)
  have hg_deriv : ∀ u ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt g (g' u) (Set.Ioi 0) u := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt hu
    have h1 : HasDerivAt (fun x : ℝ => a * x) a u := by
      simpa using (hasDerivAt_id u).const_mul a
    have h2 : HasDerivAt (fun x : ℝ => (b / 2) * x⁻¹) (-(b / 2) * (u ^ 2)⁻¹) u := by
      simpa [mul_neg] using (hasDerivAt_inv hu0).const_mul (b / 2)
    have hsub := h1.sub h2
    have hfun : ((fun x : ℝ => a * x) - (fun x : ℝ => (b / 2) * x⁻¹)) = g := by
      ext x; simp only [g, Pi.sub_apply]; ring
    rw [hfun] at hsub
    have hval : a - -(b / 2) * (u ^ 2)⁻¹ = g' u := by simp only [g']; ring
    rw [hval] at hsub
    exact hsub.hasDerivWithinAt
  have hg_strict : StrictMonoOn g (Set.Ioi 0) := by
    intro u hu v hv huv
    have hu' : 0 < u := hu
    have hv' : 0 < v := hv
    simp only [g]
    have h1 : a * u < a * v := mul_lt_mul_of_pos_left huv ha
    have h2 : b / (2 * v) < b / (2 * u) :=
      div_lt_div_of_pos_left hb (by positivity) (by linarith)
    linarith
  have hg_img : g '' Set.Ioi 0 = Set.univ := by
    ext y
    simp only [Set.mem_image, Set.mem_Ioi, Set.mem_univ, iff_true]
    have hdisc : 0 < y ^ 2 + 2 * a * b := by positivity
    set u : ℝ := (y + Real.sqrt (y ^ 2 + 2 * a * b)) / (2 * a)
    have hu_pos : 0 < u := by
      have hgt : |y| < Real.sqrt (y ^ 2 + 2 * a * b) := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_lt_sqrt (sq_nonneg y) (by linarith [mul_pos ha hb])
      have hnum : 0 < y + Real.sqrt (y ^ 2 + 2 * a * b) := by linarith [neg_abs_le y]
      exact div_pos hnum (by positivity)
    refine ⟨u, hu_pos, ?_⟩
    have hsq : Real.sqrt (y ^ 2 + 2 * a * b) ^ 2 = y ^ 2 + 2 * a * b := Real.sq_sqrt hdisc.le
    have h2au : 2 * a * u = y + Real.sqrt (y ^ 2 + 2 * a * b) := by
      simp only [u]; field_simp [ha.ne']
    have hquad : 2 * a * u ^ 2 - b = y * (2 * u) := by
      have hmul : (2 * a) * (2 * a * u ^ 2 - b) = (2 * a) * (y * (2 * u)) := by
        have h2sq : (2 * a * u) ^ 2 = (y + Real.sqrt (y ^ 2 + 2 * a * b)) ^ 2 := by rw [h2au]
        linear_combination h2sq + hsq - 2 * y * h2au
      exact mul_left_cancel₀ (by positivity : 2 * a ≠ 0) hmul
    simp only [g]
    have h2u : 2 * u ≠ 0 := by positivity
    rw [show a * u - b / (2 * u) = (2 * a * u ^ 2 - b) / (2 * u) by field_simp [h2u]]
    rw [div_eq_iff h2u]
    exact hquad
  have hgauss_int : Integrable (fun s : ℝ => Real.exp (-(s ^ 2))) := by
    simpa using integrable_exp_neg_mul_sq (show (0 : ℝ) < 1 by norm_num)
  have hgauss_val : (∫ s : ℝ, Real.exp (-(s ^ 2))) = Real.sqrt Real.pi := by
    simpa using integral_gaussian (1 : ℝ)
  have hch_int : IntegrableOn (fun u : ℝ => |g' u| * Real.exp (-(g u ^ 2))) (Set.Ioi 0) := by
    have h := (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ioi hg_deriv hg_strict.injOn (fun s : ℝ => Real.exp (-(s ^ 2)))).mp
    rw [hg_img, integrableOn_univ] at h
    simpa [smul_eq_mul] using h hgauss_int
  have hch_val : (∫ u in Set.Ioi (0 : ℝ), |g' u| * Real.exp (-(g u ^ 2))) = Real.sqrt Real.pi := by
    have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      measurableSet_Ioi hg_deriv hg_strict.injOn (fun s : ℝ => Real.exp (-(s ^ 2)))
    rw [hg_img, Measure.restrict_univ, hgauss_val] at h
    simpa [smul_eq_mul] using h.symm
  have hint_exp : IntegrableOn (fun u : ℝ => Real.exp (-(g u ^ 2))) (Set.Ioi 0) := by
    have hmeas : AEStronglyMeasurable (fun u : ℝ => Real.exp (-(g u ^ 2))) (volume.restrict (Set.Ioi 0)) := by
      have hc : ContinuousOn (fun u : ℝ => Real.exp (-(g u ^ 2))) (Set.Ioi 0) := by
        intro u hu
        have hu' : 0 < u := hu
        have h1 : ContinuousAt (fun x : ℝ => a * x - b / (2 * x)) u :=
          (continuous_const.mul continuous_id).continuousAt.sub
            (continuousAt_const.div (continuous_const.mul continuous_id).continuousAt (by positivity))
        exact (Real.continuous_exp.continuousAt.comp (continuous_neg.continuousAt.comp ((h1.pow 2)))).continuousWithinAt
      exact hc.aestronglyMeasurable measurableSet_Ioi
    refine Integrable.mono' (hch_int.const_mul a⁻¹) hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu' : 0 < u := hu
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    have hg'_pos : a ≤ g' u := by simp only [g']; linarith [div_pos hb (show 0 < 2 * u ^ 2 by positivity)]
    have hg'_abs : |g' u| = g' u := abs_of_pos (lt_of_lt_of_le ha hg'_pos)
    rw [hg'_abs]
    calc Real.exp (-(g u ^ 2))
        = a⁻¹ * (a * Real.exp (-(g u ^ 2))) := by field_simp [ha.ne']
      _ ≤ a⁻¹ * (g' u * Real.exp (-(g u ^ 2))) := by gcongr
  let φ : ℝ → ℝ := fun v => b / (2 * a * v)
  let φ' : ℝ → ℝ := fun v => -b / (2 * a * v ^ 2)
  have hφ_deriv : ∀ v ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt φ (φ' v) (Set.Ioi 0) v := by
    intro v hv
    have hv0 : v ≠ 0 := ne_of_gt hv
    have h := (hasDerivAt_inv hv0).const_mul (b / (2 * a))
    have hfun : (fun x : ℝ => (b / (2 * a)) * x⁻¹) = φ := by ext x; simp only [φ]; ring
    rw [hfun] at h
    have hval : (b / (2 * a)) * -(v ^ 2)⁻¹ = φ' v := by simp only [φ']; ring
    rw [hval] at h
    exact h.hasDerivWithinAt
  have hφ_inj : Set.InjOn φ (Set.Ioi 0) := by
    intro u hu v hv heq
    have hu' : 0 < u := hu
    have hv' : 0 < v := hv
    simp only [φ] at heq
    have h1 := (div_eq_div_iff (show 2 * a * u ≠ 0 by positivity) (show 2 * a * v ≠ 0 by positivity)).mp heq
    have h2 : 2 * a * v = 2 * a * u := mul_left_cancel₀ hb.ne' h1
    nlinarith
  have hφ_img : φ '' Set.Ioi 0 = Set.Ioi 0 := by
    ext u
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨v, hv, rfl⟩; simp only [φ]; positivity
    · intro hu; refine ⟨b / (2 * a * u), by positivity, ?_⟩
      simp only [φ]; field_simp [ha.ne', hb.ne', hu.ne']
  have hinv_eq : (∫ u in Set.Ioi (0 : ℝ), Real.exp (-(g u ^ 2))) =
      ∫ v in Set.Ioi (0 : ℝ), (b / (2 * a * v ^ 2)) * Real.exp (-(g v ^ 2)) := by
    have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      measurableSet_Ioi hφ_deriv hφ_inj (fun u : ℝ => Real.exp (-(g u ^ 2)))
    rw [hφ_img] at h
    rw [h]
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    have hv' : 0 < v := hv
    have hpos : 0 < b / (2 * a * v ^ 2) := by positivity
    have habs : |φ' v| = b / (2 * a * v ^ 2) := by
      simp only [φ', neg_div, abs_neg, abs_of_pos hpos]
    have hgφ : g (φ v) = -g v := by
      simp only [g, φ]; field_simp [ha.ne', hb.ne', hv'.ne']; ring
    simp only [smul_eq_mul, habs, hgφ, neg_sq]
  have hint_second : IntegrableOn (fun v : ℝ => (b / (2 * a * v ^ 2)) * Real.exp (-(g v ^ 2))) (Set.Ioi 0) := by
    have h := (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ioi hφ_deriv hφ_inj (fun u : ℝ => Real.exp (-(g u ^ 2)))).mp
    rw [hφ_img] at h
    refine (h hint_exp).congr_fun (fun v hv => ?_) measurableSet_Ioi
    have hv' : 0 < v := hv
    have hpos : 0 < b / (2 * a * v ^ 2) := by positivity
    have habs : |φ' v| = b / (2 * a * v ^ 2) := by
      simp only [φ', neg_div, abs_neg, abs_of_pos hpos]
    have hgφ : g (φ v) = -g v := by
      simp only [g, φ]; field_simp [ha.ne', hb.ne', hv'.ne']; ring
    simp only [smul_eq_mul, habs, hgφ, neg_sq]
  have hsum : 2 * (∫ u in Set.Ioi (0 : ℝ), Real.exp (-(g u ^ 2))) = Real.sqrt Real.pi / a := by
    have h1 : (∫ u in Set.Ioi (0 : ℝ), Real.exp (-(g u ^ 2))) +
        (∫ v in Set.Ioi (0 : ℝ), (b / (2 * a * v ^ 2)) * Real.exp (-(g v ^ 2))) =
        ∫ u in Set.Ioi (0 : ℝ), (1 + b / (2 * a * u ^ 2)) * Real.exp (-(g u ^ 2)) := by
      rw [← integral_add hint_exp hint_second]
      congr 1; ext u; ring
    have h2 : (∫ u in Set.Ioi (0 : ℝ), (1 + b / (2 * a * u ^ 2)) * Real.exp (-(g u ^ 2))) =
        a⁻¹ * (∫ u in Set.Ioi (0 : ℝ), |g' u| * Real.exp (-(g u ^ 2))) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
      have hu' : 0 < u := hu
      have hg'_pos : 0 < g' u := by simp only [g']; positivity
      rw [abs_of_pos hg'_pos]
      simp only [g']; field_simp [ha.ne', hu'.ne']
    rw [← hinv_eq] at h1
    rw [hch_val] at h2
    have h3 : 2 * (∫ u in Set.Ioi (0 : ℝ), Real.exp (-(g u ^ 2))) = a⁻¹ * Real.sqrt Real.pi := by
      linarith
    rw [h3, div_eq_inv_mul]
  refine ⟨?_, hint_exp⟩
  have hfinal : (∫ u in Set.Ioi (0 : ℝ), Real.exp (-(g u ^ 2))) = Real.sqrt Real.pi / (2 * a) := by
    rw [show Real.sqrt Real.pi / (2 * a) = (Real.sqrt Real.pi / a) / 2 by ring, ← hsum]; ring
  exact hfinal

private lemma glaisher_half (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ t in Set.Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * Real.exp (-(a ^ 2 * t + b ^ 2 / (4 * t)))) =
      Real.sqrt Real.pi / a * Real.exp (-(a * b)) ∧
    IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * Real.exp (-(a ^ 2 * t + b ^ 2 / (4 * t)))) (Set.Ioi 0) := by
  let ψ : ℝ → ℝ := fun u => u ^ 2
  let ψ' : ℝ → ℝ := fun u => 2 * u
  have hψ_deriv : ∀ u ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt ψ (ψ' u) (Set.Ioi 0) u := by
    intro u _; simpa [ψ, ψ'] using (hasDerivAt_pow 2 u).hasDerivWithinAt
  have hψ_inj : Set.InjOn ψ (Set.Ioi 0) := by
    intro u hu v hv heq; simp only [ψ] at heq; nlinarith [Set.mem_Ioi.mp hu, Set.mem_Ioi.mp hv]
  have hψ_img : ψ '' Set.Ioi 0 = Set.Ioi 0 := by
    ext t; simp only [Set.mem_image, Set.mem_Ioi, ψ]
    constructor
    · rintro ⟨u, hu, rfl⟩; positivity
    · intro ht; exact ⟨Real.sqrt t, Real.sqrt_pos.mpr ht, Real.sq_sqrt ht.le⟩
  have hcore := glaisher_core a b ha hb
  have hstep : ∀ u ∈ Set.Ioi (0 : ℝ),
      |ψ' u| * ((ψ u) ^ (-(1 / 2 : ℝ)) * Real.exp (-(a ^ 2 * ψ u + b ^ 2 / (4 * ψ u)))) =
      (2 * Real.exp (-(a * b))) * Real.exp (-((a * u - b / (2 * u)) ^ 2)) := by
    intro u hu
    have hu_pos : 0 < u := hu
    have habs : |ψ' u| = 2 * u := abs_of_pos (by simp only [ψ']; positivity)
    have hrpow : (u ^ 2) ^ (-(1 / 2 : ℝ)) = u⁻¹ := by
      rw [← Real.rpow_natCast u 2, ← Real.rpow_mul hu_pos.le]
      norm_num
      exact Real.rpow_neg_one u
    rw [habs, show ψ u = u ^ 2 from rfl, hrpow]
    have hcancel : 2 * u * u⁻¹ = 2 := by field_simp [hu_pos.ne']
    have hexp : -(a ^ 2 * u ^ 2 + b ^ 2 / (4 * u ^ 2)) = -(a * b) + -((a * u - b / (2 * u)) ^ 2) := by
      field_simp [hu_pos.ne']; ring
    rw [← mul_assoc, hcancel, hexp, Real.exp_add]; ring
  have hch_val := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi hψ_deriv hψ_inj
    (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * Real.exp (-(a ^ 2 * t + b ^ 2 / (4 * t))))
  rw [hψ_img] at hch_val
  have hch_int := MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi hψ_deriv hψ_inj
    (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * Real.exp (-(a ^ 2 * t + b ^ 2 / (4 * t))))
  rw [hψ_img] at hch_int
  constructor
  · rw [hch_val]
    have hcongr : (∫ u in Set.Ioi (0 : ℝ),
        |ψ' u| • (ψ u ^ (-(1 / 2 : ℝ)) * Real.exp (-(a ^ 2 * ψ u + b ^ 2 / (4 * ψ u))))) =
      ∫ u in Set.Ioi (0 : ℝ), (2 * Real.exp (-(a * b))) * Real.exp (-((a * u - b / (2 * u)) ^ 2)) :=
      setIntegral_congr_fun measurableSet_Ioi fun u hu => by simpa [smul_eq_mul] using hstep u hu
    rw [hcongr, integral_const_mul, hcore.1]
    field_simp [ha.ne']
  · rw [hch_int]
    refine IntegrableOn.congr_fun (hcore.2.const_mul (2 * Real.exp (-(a * b)))) (fun u hu => ?_) measurableSet_Ioi
    simpa [smul_eq_mul] using (hstep u hu).symm

private lemma glaisher_three_halves (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) * Real.exp (-(a ^ 2 * t + b ^ 2 / (4 * t)))) =
      2 * Real.sqrt Real.pi / b * Real.exp (-(a * b)) := by
  let c : ℝ := b ^ 2 / (4 * a ^ 2)
  have hc : 0 < c := by positivity
  let φ : ℝ → ℝ := fun s => c / s
  let φ' : ℝ → ℝ := fun s => -c / s ^ 2
  have hφ_deriv : ∀ s ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt φ (φ' s) (Set.Ioi 0) s := by
    intro s hs
    have h := (hasDerivAt_inv (ne_of_gt hs)).const_mul c
    have hfun : (fun x : ℝ => c * x⁻¹) = φ := by ext x; simp only [φ]; ring
    rw [hfun] at h
    have hval : c * -(s ^ 2)⁻¹ = φ' s := by simp only [φ']; ring
    rw [hval] at h
    exact h.hasDerivWithinAt
  have hφ_inj : Set.InjOn φ (Set.Ioi 0) := by
    intro u hu v hv heq
    have hu' : 0 < u := hu
    have hv' : 0 < v := hv
    simp only [φ] at heq
    have h1 := (div_eq_div_iff hu'.ne' hv'.ne').mp heq
    nlinarith
  have hφ_img : φ '' Set.Ioi 0 = Set.Ioi 0 := by
    ext t; simp only [Set.mem_image, Set.mem_Ioi, φ]
    constructor
    · rintro ⟨s, hs, rfl⟩; positivity
    · intro ht; exact ⟨c / t, by positivity, by field_simp [ht.ne', hc.ne']⟩
  have hch := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi hφ_deriv hφ_inj
    (fun t : ℝ => t ^ (-(3 / 2 : ℝ)) * Real.exp (-(a ^ 2 * t + b ^ 2 / (4 * t))))
  rw [hφ_img] at hch
  rw [hch]
  have hcongr : (∫ s in Set.Ioi (0 : ℝ),
      |φ' s| • (φ s ^ (-(3 / 2 : ℝ)) * Real.exp (-(a ^ 2 * φ s + b ^ 2 / (4 * φ s))))) =
    ∫ s in Set.Ioi (0 : ℝ), (2 * a / b) * (s ^ (-(1 / 2 : ℝ)) * Real.exp (-(a ^ 2 * s + b ^ 2 / (4 * s)))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs_pos : 0 < s := hs
    have habs : |φ' s| = c / s ^ 2 := by
      simp only [φ', neg_div, abs_neg, abs_of_pos (div_pos hc (sq_pos_of_pos hs_pos))]
    have hrpow : (c / s) ^ (-(3 / 2 : ℝ)) = c ^ (-(3 / 2 : ℝ)) * s ^ (3 / 2 : ℝ) := by
      rw [Real.div_rpow hc.le hs_pos.le, Real.rpow_neg hs_pos.le, div_inv_eq_mul]
    have hc_pow : c * c ^ (-(3 / 2 : ℝ)) = 2 * a / b := by
      have h1 : c * c ^ (-(3 / 2 : ℝ)) = c ^ (-(1 / 2 : ℝ)) := by
        conv_lhs => arg 1; rw [← Real.rpow_one c]
        rw [← Real.rpow_add hc]; norm_num
      rw [h1]
      have h2 : c = (b / (2 * a)) ^ 2 := by simp only [c]; ring
      rw [h2, ← Real.rpow_natCast (b / (2 * a)) 2, ← Real.rpow_mul (by positivity)]
      norm_num
      rw [Real.rpow_neg_one, inv_div]
    have hs_pow : (s ^ 2)⁻¹ * s ^ (3 / 2 : ℝ) = s ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast s 2, ← Real.rpow_neg hs_pos.le, ← Real.rpow_add hs_pos]
      norm_num
    have hexp : a ^ 2 * (c / s) + b ^ 2 / (4 * (c / s)) = a ^ 2 * s + b ^ 2 / (4 * s) := by
      simp only [c]; field_simp [ha.ne', hb.ne', hs_pos.ne']; ring
    simp only [smul_eq_mul, habs, show φ s = c / s from rfl, hrpow, hexp]
    calc c / s ^ 2 * (c ^ (-(3 / 2 : ℝ)) * s ^ (3 / 2 : ℝ) * Real.exp (-(a ^ 2 * s + b ^ 2 / (4 * s))))
        = (c * c ^ (-(3 / 2 : ℝ))) * ((s ^ 2)⁻¹ * s ^ (3 / 2 : ℝ)) *
            Real.exp (-(a ^ 2 * s + b ^ 2 / (4 * s))) := by ring
      _ = (2 * a / b) * (s ^ (-(1 / 2 : ℝ)) * Real.exp (-(a ^ 2 * s + b ^ 2 / (4 * s)))) := by
          rw [hc_pow, hs_pow]; ring
  rw [hcongr, integral_const_mul, (glaisher_half a b ha hb).1]
  field_simp [ha.ne', hb.ne']

/-! ### Part 3: Sommerfeld identity on the positive imaginary axis -/

private lemma sommerfeldRoot_pure_imag (κ : ℝ) (hκ : 0 < κ) (ξ η : ℝ) :
    sommerfeldRoot (Complex.I * κ) ξ η = (Real.sqrt (ξ ^ 2 + η ^ 2 + κ ^ 2) : ℂ) := by
  unfold sommerfeldRoot
  have hz : (ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - (Complex.I * (κ : ℂ)) ^ 2 =
      ((ξ ^ 2 + η ^ 2 + κ ^ 2 : ℝ) : ℂ) := by
    push_cast; ring_nf; simp [Complex.I_sq]
  have hpos : 0 < ξ ^ 2 + η ^ 2 + κ ^ 2 := by positivity
  rw [hz]
  have hnot : ¬((((ξ ^ 2 + η ^ 2 + κ ^ 2 : ℝ) : ℂ)).im = 0 ∧ (((ξ ^ 2 + η ^ 2 + κ ^ 2 : ℝ) : ℂ)).re < 0) := by
    simp only [Complex.ofReal_im, Complex.ofReal_re, true_and, not_lt]; exact hpos.le
  rw [if_neg hnot, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hpos.le]
  norm_cast
  rw [Real.sqrt_eq_rpow]

private lemma sommerfeld_pure_imag (κ : ℝ) (hκ : 0 < κ) (r : Space) (hr : 0 < r 2) :
    greenFn (Complex.I * κ) r =
      ∫ ζ : ℝ × ℝ, ghat (Complex.I * κ) ζ.1 ζ.2 (r 2) * planeWave ζ.1 ζ.2 (r 0) (r 1) := by
  set z : ℝ := r 2
  have hz : 0 < z := hr
  have hr_pos : 0 < ‖r‖ := by
    have h := PiLp.norm_apply_le r (2 : Fin 3)
    rw [Real.norm_eq_abs, abs_of_pos hz] at h
    exact lt_of_lt_of_le hz h
  have hghat_int : ∀ ζ : ℝ × ℝ,
      ghat (Complex.I * κ) ζ.1 ζ.2 z =
        ((1 / (8 * Real.pi ^ 2 * Real.sqrt Real.pi) : ℝ) : ℂ) *
          ∫ t in Set.Ioi (0 : ℝ),
            ((t ^ (-(1 / 2 : ℝ)) * Real.exp (-((ζ.1 ^ 2 + ζ.2 ^ 2 + κ ^ 2) * t + z ^ 2 / (4 * t))) : ℝ) : ℂ) := by
    intro ζ
    set a : ℝ := Real.sqrt (ζ.1 ^ 2 + ζ.2 ^ 2 + κ ^ 2)
    have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
    have ha2 : a ^ 2 = ζ.1 ^ 2 + ζ.2 ^ 2 + κ ^ 2 := Real.sq_sqrt (by positivity)
    have hval := (glaisher_half a z ha hz).1
    rw [ha2] at hval
    have hcoe : (∫ t in Set.Ioi (0 : ℝ),
        ((t ^ (-(1 / 2 : ℝ)) * Real.exp (-((ζ.1 ^ 2 + ζ.2 ^ 2 + κ ^ 2) * t + z ^ 2 / (4 * t))) : ℝ) : ℂ)) =
        ((∫ t in Set.Ioi (0 : ℝ),
          t ^ (-(1 / 2 : ℝ)) * Real.exp (-((ζ.1 ^ 2 + ζ.2 ^ 2 + κ ^ 2) * t + z ^ 2 / (4 * t))) : ℝ) : ℂ) :=
      integral_ofReal
    rw [hcoe, hval]
    simp only [ghat, sommerfeldRoot_pure_imag κ hκ, abs_of_pos hz]
    push_cast
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hsqpi : (Real.sqrt Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hac : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
    simp only [a] at hac ⊢
    rw [neg_mul]
    field_simp [hpi, hsqpi, hac]
  let K : (ℝ × ℝ) → ℝ → ℂ := fun ζ t =>
    ((t ^ (-(1 / 2 : ℝ)) * Real.exp (-((ζ.1 ^ 2 + ζ.2 ^ 2 + κ ^ 2) * t + z ^ 2 / (4 * t))) : ℝ) : ℂ) *
      planeWave ζ.1 ζ.2 (r 0) (r 1)
  have hinner_t : ∀ t : ℝ, 0 < t →
      (∫ ζ : ℝ × ℝ, K ζ t) =
        ((Real.pi * t ^ (-(3 / 2 : ℝ)) * Real.exp (-(κ ^ 2 * t + ‖r‖ ^ 2 / (4 * t))) : ℝ) : ℂ) := by
    intro t ht
    have h1d : ∀ x : ℝ, (∫ ξ : ℝ,
        ((Real.exp (-(t * ξ ^ 2)) : ℝ) : ℂ) * Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ))) =
        ((Real.sqrt (Real.pi / t) * Real.exp (-(x ^ 2 / (4 * t))) : ℝ) : ℂ) := by
      intro x
      have hfg := fourierIntegral_gaussian (b := (t : ℂ)) (by simpa using ht) (x : ℂ)
      have hLHS : (∫ ξ : ℝ, Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ)) * Complex.exp (-(t : ℂ) * (ξ : ℂ) ^ 2)) =
          ∫ ξ : ℝ, ((Real.exp (-(t * ξ ^ 2)) : ℝ) : ℂ) * Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ)) := by
        congr 1; ext ξ
        rw [Complex.ofReal_exp]
        push_cast; ring_nf
      rw [hLHS] at hfg
      rw [hfg]
      have hdiv : ((Real.pi : ℂ) / (t : ℂ)) ^ (1 / 2 : ℂ) = (Real.sqrt (Real.pi / t) : ℂ) := by
        rw [← Complex.ofReal_div, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
          ← Complex.ofReal_cpow (div_nonneg Real.pi_pos.le ht.le)]
        norm_cast; rw [Real.sqrt_eq_rpow]
      rw [hdiv, show -((x : ℂ) ^ 2) / (4 * (t : ℂ)) = ((-(x ^ 2 / (4 * t)) : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_exp, ← Complex.ofReal_mul]
    have hK_split : ∀ ζ : ℝ × ℝ, K ζ t =
        ((t ^ (-(1 / 2 : ℝ)) * Real.exp (-(κ ^ 2 * t + z ^ 2 / (4 * t))) : ℝ) : ℂ) *
        ((((Real.exp (-(t * ζ.1 ^ 2)) : ℝ) : ℂ) * Complex.exp (Complex.I * (ζ.1 : ℂ) * (r 0 : ℂ))) *
         (((Real.exp (-(t * ζ.2 ^ 2)) : ℝ) : ℂ) * Complex.exp (Complex.I * (ζ.2 : ℂ) * (r 1 : ℂ)))) := by
      intro ζ
      simp only [K, planeWave]
      have hre : -((ζ.1 ^ 2 + ζ.2 ^ 2 + κ ^ 2) * t + z ^ 2 / (4 * t)) =
          -(κ ^ 2 * t + z ^ 2 / (4 * t)) + (-(t * ζ.1 ^ 2) + -(t * ζ.2 ^ 2)) := by ring
      rw [hre, Real.exp_add, Real.exp_add]
      have hpw : Complex.I * ((ζ.1 : ℂ) * (r 0 : ℂ) + (ζ.2 : ℂ) * (r 1 : ℂ)) =
          Complex.I * (ζ.1 : ℂ) * (r 0 : ℂ) + Complex.I * (ζ.2 : ℂ) * (r 1 : ℂ) := by ring
      rw [hpw, Complex.exp_add]
      push_cast; ring
    simp_rw [hK_split, integral_const_mul]
    rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
      MeasureTheory.integral_prod_mul
        (f := fun ξ : ℝ => ((Real.exp (-(t * ξ ^ 2)) : ℝ) : ℂ) * Complex.exp (Complex.I * (ξ : ℂ) * (r 0 : ℂ)))
        (g := fun η : ℝ => ((Real.exp (-(t * η ^ 2)) : ℝ) : ℂ) * Complex.exp (Complex.I * (η : ℂ) * (r 1 : ℂ))),
      h1d (r 0), h1d (r 1)]
    have hr_sq : ‖r‖ ^ 2 = r 0 ^ 2 + r 1 ^ 2 + z ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [Fin.sum_univ_three, z]
    have hsq : Real.sqrt (Real.pi / t) * Real.sqrt (Real.pi / t) = Real.pi / t :=
      Real.mul_self_sqrt (by positivity)
    have htpow : t ^ (-(1 / 2 : ℝ)) * t⁻¹ = t ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_neg_one t, ← Real.rpow_add ht]; norm_num
    simp_rw [← Complex.ofReal_mul]
    congr 1
    rw [show t ^ (-(1 / 2 : ℝ)) * Real.exp (-(κ ^ 2 * t + z ^ 2 / (4 * t))) *
        (Real.sqrt (Real.pi / t) * Real.exp (-(r 0 ^ 2 / (4 * t))) *
          (Real.sqrt (Real.pi / t) * Real.exp (-(r 1 ^ 2 / (4 * t))))) =
        Real.pi * (t ^ (-(1 / 2 : ℝ)) * t⁻¹) *
          (Real.exp (-(κ ^ 2 * t + z ^ 2 / (4 * t))) * Real.exp (-(r 0 ^ 2 / (4 * t))) *
            Real.exp (-(r 1 ^ 2 / (4 * t)))) by
      calc t ^ (-(1 / 2 : ℝ)) * Real.exp (-(κ ^ 2 * t + z ^ 2 / (4 * t))) *
              (Real.sqrt (Real.pi / t) * Real.exp (-(r 0 ^ 2 / (4 * t))) *
                (Real.sqrt (Real.pi / t) * Real.exp (-(r 1 ^ 2 / (4 * t)))))
          = t ^ (-(1 / 2 : ℝ)) * (Real.sqrt (Real.pi / t) * Real.sqrt (Real.pi / t)) *
              (Real.exp (-(κ ^ 2 * t + z ^ 2 / (4 * t))) * Real.exp (-(r 0 ^ 2 / (4 * t))) *
                Real.exp (-(r 1 ^ 2 / (4 * t)))) := by ring
        _ = Real.pi * (t ^ (-(1 / 2 : ℝ)) * t⁻¹) *
              (Real.exp (-(κ ^ 2 * t + z ^ 2 / (4 * t))) * Real.exp (-(r 0 ^ 2 / (4 * t))) *
                Real.exp (-(r 1 ^ 2 / (4 * t)))) := by rw [hsq]; ring]
    rw [htpow, ← Real.exp_add, ← Real.exp_add, hr_sq]
    congr 2; ring
  have hK_int : Integrable (Function.uncurry K) (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    have hK_meas : AEStronglyMeasurable (Function.uncurry K)
        (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
      have hm1 : Measurable (fun p : (ℝ × ℝ) × ℝ =>
          p.2 ^ (-(1 / 2 : ℝ)) * Real.exp (-((p.1.1 ^ 2 + p.1.2 ^ 2 + κ ^ 2) * p.2 + z ^ 2 / (4 * p.2)))) := by
        fun_prop
      have hm2 : Measurable (fun p : (ℝ × ℝ) × ℝ => planeWave p.1.1 p.1.2 (r 0) (r 1)) := by
        unfold planeWave; fun_prop
      exact ((Complex.continuous_ofReal.measurable.comp hm1).mul hm2).aestronglyMeasurable
    rw [integrable_prod_iff' hK_meas]
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht_pos : 0 < t := ht
      have hmeas_t : AEStronglyMeasurable (fun ζ : ℝ × ℝ => K ζ t) volume := by
        have h1 : Measurable (fun ζ : ℝ × ℝ =>
            t ^ (-(1 / 2 : ℝ)) * Real.exp (-((ζ.1 ^ 2 + ζ.2 ^ 2 + κ ^ 2) * t + z ^ 2 / (4 * t)))) := by
          fun_prop
        have h2 : Measurable (fun ζ : ℝ × ℝ => planeWave ζ.1 ζ.2 (r 0) (r 1)) := by
          unfold planeWave; fun_prop
        exact ((Complex.continuous_ofReal.measurable.comp h1).mul h2).aestronglyMeasurable
      have hbound_int : Integrable (fun ζ : ℝ × ℝ =>
          (t ^ (-(1 / 2 : ℝ)) * Real.exp (-(κ ^ 2 * t + z ^ 2 / (4 * t)))) *
          (Real.exp (-t * ζ.1 ^ 2) * Real.exp (-t * ζ.2 ^ 2))) volume := by
        rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl]
        exact ((integrable_exp_neg_mul_sq ht_pos).mul_prod (integrable_exp_neg_mul_sq ht_pos)).const_mul _
      refine Integrable.mono' hbound_int hmeas_t (Eventually.of_forall fun ζ => ?_)
      simp only [Function.uncurry_apply_pair, K, norm_mul, norm_planeWave, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht_pos.le _) (Real.exp_nonneg _))]
      have hre : -((ζ.1 ^ 2 + ζ.2 ^ 2 + κ ^ 2) * t + z ^ 2 / (4 * t)) =
          -(κ ^ 2 * t + z ^ 2 / (4 * t)) + (-t * ζ.1 ^ 2 + -t * ζ.2 ^ 2) := by ring
      rw [hre, Real.exp_add, Real.exp_add]
      exact le_of_eq (by ring)
    · have hnorm_t : ∀ t ∈ Set.Ioi (0 : ℝ), (∫ ζ : ℝ × ℝ, ‖K ζ t‖) =
          Real.pi * t ^ (-(3 / 2 : ℝ)) * Real.exp (-(κ ^ 2 * t + z ^ 2 / (4 * t))) := by
        intro t ht
        have ht_pos : 0 < t := ht
        have hnorm_eq : (fun ζ : ℝ × ℝ => ‖K ζ t‖) = fun ζ =>
            (t ^ (-(1 / 2 : ℝ)) * Real.exp (-(κ ^ 2 * t + z ^ 2 / (4 * t)))) *
            (Real.exp (-t * ζ.1 ^ 2) * Real.exp (-t * ζ.2 ^ 2)) := by
          ext ζ
          simp only [K, norm_mul, norm_planeWave, mul_one, Complex.norm_real,
            Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht_pos.le _) (Real.exp_nonneg _))]
          have hre : -((ζ.1 ^ 2 + ζ.2 ^ 2 + κ ^ 2) * t + z ^ 2 / (4 * t)) =
              -(κ ^ 2 * t + z ^ 2 / (4 * t)) + (-t * ζ.1 ^ 2 + -t * ζ.2 ^ 2) := by ring
          rw [hre, Real.exp_add, Real.exp_add]; ring
        rw [hnorm_eq, integral_const_mul, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
          MeasureTheory.integral_prod_mul (f := fun ξ : ℝ => Real.exp (-t * ξ ^ 2))
            (g := fun η : ℝ => Real.exp (-t * η ^ 2)),
          integral_gaussian t]
        have hsq : Real.sqrt (Real.pi / t) * Real.sqrt (Real.pi / t) = Real.pi / t :=
          Real.mul_self_sqrt (by positivity)
        have htpow : t ^ (-(1 / 2 : ℝ)) * t⁻¹ = t ^ (-(3 / 2 : ℝ)) := by
          rw [← Real.rpow_neg_one t, ← Real.rpow_add ht_pos]; norm_num
        calc t ^ (-(1 / 2 : ℝ)) * Real.exp (-(κ ^ 2 * t + z ^ 2 / (4 * t))) *
              (Real.sqrt (Real.pi / t) * Real.sqrt (Real.pi / t))
            = Real.pi * (t ^ (-(1 / 2 : ℝ)) * t⁻¹) * Real.exp (-(κ ^ 2 * t + z ^ 2 / (4 * t))) := by
              rw [hsq]; ring
          _ = Real.pi * t ^ (-(3 / 2 : ℝ)) * Real.exp (-(κ ^ 2 * t + z ^ 2 / (4 * t))) := by
              rw [htpow]
      have hint_32 : IntegrableOn (fun t : ℝ =>
          Real.pi * t ^ (-(3 / 2 : ℝ)) * Real.exp (-(κ ^ 2 * t + z ^ 2 / (4 * t)))) (Set.Ioi 0) := by
        let c : ℝ := z ^ 2 / (4 * κ ^ 2)
        have hc : 0 < c := by positivity
        let φ : ℝ → ℝ := fun s => c / s
        let φ' : ℝ → ℝ := fun s => -c / s ^ 2
        have hφ_deriv : ∀ s ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt φ (φ' s) (Set.Ioi 0) s := by
          intro s hs
          have h := (hasDerivAt_inv (ne_of_gt hs)).const_mul c
          have hfun : (fun x : ℝ => c * x⁻¹) = φ := by ext x; simp only [φ]; ring
          rw [hfun] at h
          have hval : c * -(s ^ 2)⁻¹ = φ' s := by simp only [φ']; ring
          rw [hval] at h; exact h.hasDerivWithinAt
        have hφ_inj : Set.InjOn φ (Set.Ioi 0) := by
          intro u hu v hv heq
          have hu' : 0 < u := hu
          have hv' : 0 < v := hv
          simp only [φ] at heq
          have h1 := (div_eq_div_iff hu'.ne' hv'.ne').mp heq
          nlinarith
        have hφ_img : φ '' Set.Ioi 0 = Set.Ioi 0 := by
          ext t; simp only [Set.mem_image, Set.mem_Ioi, φ]
          constructor
          · rintro ⟨s, hs, rfl⟩; positivity
          · intro ht; exact ⟨c / t, by positivity, by field_simp [ht.ne', hc.ne']⟩
        have hch := MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
          measurableSet_Ioi hφ_deriv hφ_inj
          (fun t : ℝ => Real.pi * t ^ (-(3 / 2 : ℝ)) * Real.exp (-(κ ^ 2 * t + z ^ 2 / (4 * t))))
        rw [hφ_img] at hch; rw [hch]
        refine IntegrableOn.congr_fun ((glaisher_half κ z hκ hz).2.const_mul (Real.pi * (2 * κ / z)))
          (fun s hs => ?_) measurableSet_Ioi
        have hs_pos : 0 < s := hs
        have habs : |φ' s| = c / s ^ 2 := by
          simp only [φ', neg_div, abs_neg, abs_of_pos (div_pos hc (sq_pos_of_pos hs_pos))]
        have hrpow : (c / s) ^ (-(3 / 2 : ℝ)) = c ^ (-(3 / 2 : ℝ)) * s ^ (3 / 2 : ℝ) := by
          rw [Real.div_rpow hc.le hs_pos.le, Real.rpow_neg hs_pos.le, div_inv_eq_mul]
        have hc_pow : c * c ^ (-(3 / 2 : ℝ)) = 2 * κ / z := by
          have h1 : c * c ^ (-(3 / 2 : ℝ)) = c ^ (-(1 / 2 : ℝ)) := by
            conv_lhs => arg 1; rw [← Real.rpow_one c]
            rw [← Real.rpow_add hc]; norm_num
          rw [h1]
          have h2 : c = (z / (2 * κ)) ^ 2 := by simp only [c]; ring
          rw [h2, ← Real.rpow_natCast (z / (2 * κ)) 2, ← Real.rpow_mul (by positivity)]
          norm_num; rw [Real.rpow_neg_one, inv_div]
        have hs_pow : (s ^ 2)⁻¹ * s ^ (3 / 2 : ℝ) = s ^ (-(1 / 2 : ℝ)) := by
          rw [← Real.rpow_natCast s 2, ← Real.rpow_neg hs_pos.le, ← Real.rpow_add hs_pos]; norm_num
        have hexp : κ ^ 2 * (c / s) + z ^ 2 / (4 * (c / s)) = κ ^ 2 * s + z ^ 2 / (4 * s) := by
          simp only [c]; field_simp [hκ.ne', hz.ne', hs_pos.ne']; ring
        simp only [smul_eq_mul, habs, show φ s = c / s from rfl, hrpow, hexp]
        calc Real.pi * (2 * κ / z) * (s ^ (-(1 / 2 : ℝ)) * Real.exp (-(κ ^ 2 * s + z ^ 2 / (4 * s))))
            = Real.pi * (c * c ^ (-(3 / 2 : ℝ))) * ((s ^ 2)⁻¹ * s ^ (3 / 2 : ℝ)) *
                Real.exp (-(κ ^ 2 * s + z ^ 2 / (4 * s))) := by rw [hc_pow, hs_pow]; ring
          _ = c / s ^ 2 * (Real.pi * (c ^ (-(3 / 2 : ℝ)) * s ^ (3 / 2 : ℝ)) *
                Real.exp (-(κ ^ 2 * s + z ^ 2 / (4 * s)))) := by ring
      exact hint_32.congr_fun (fun t ht => (hnorm_t t ht).symm) measurableSet_Ioi
  have hRHS : (∫ ζ : ℝ × ℝ, ghat (Complex.I * κ) ζ.1 ζ.2 z * planeWave ζ.1 ζ.2 (r 0) (r 1)) =
      ((1 / (8 * Real.pi ^ 2 * Real.sqrt Real.pi) : ℝ) : ℂ) *
        ∫ ζ : ℝ × ℝ, ∫ t in Set.Ioi (0 : ℝ), K ζ t := by
    rw [← integral_const_mul]
    congr 1; ext ζ
    rw [hghat_int ζ, mul_assoc, ← integral_mul_const]
  rw [hRHS, MeasureTheory.integral_integral_swap hK_int]
  have hcongr_t : (∫ t in Set.Ioi (0 : ℝ), ∫ ζ : ℝ × ℝ, K ζ t) =
      ∫ t in Set.Ioi (0 : ℝ),
        ((Real.pi * t ^ (-(3 / 2 : ℝ)) * Real.exp (-(κ ^ 2 * t + ‖r‖ ^ 2 / (4 * t))) : ℝ) : ℂ) :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht => hinner_t t ht
  have hcoe_t : (∫ t in Set.Ioi (0 : ℝ),
      ((Real.pi * t ^ (-(3 / 2 : ℝ)) * Real.exp (-(κ ^ 2 * t + ‖r‖ ^ 2 / (4 * t))) : ℝ) : ℂ)) =
      ((∫ t in Set.Ioi (0 : ℝ),
        Real.pi * t ^ (-(3 / 2 : ℝ)) * Real.exp (-(κ ^ 2 * t + ‖r‖ ^ 2 / (4 * t))) : ℝ) : ℂ) :=
    integral_ofReal
  rw [hcongr_t, hcoe_t]
  have hpull : (∫ t in Set.Ioi (0 : ℝ), Real.pi * t ^ (-(3 / 2 : ℝ)) * Real.exp (-(κ ^ 2 * t + ‖r‖ ^ 2 / (4 * t)))) =
      Real.pi * ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) * Real.exp (-(κ ^ 2 * t + ‖r‖ ^ 2 / (4 * t))) := by
    rw [← integral_const_mul]; congr 1; ext t; ring
  rw [hpull, glaisher_three_halves κ ‖r‖ hκ hr_pos]
  unfold greenFn
  have hexp_eq : Complex.exp (Complex.I * (Complex.I * (κ : ℂ)) * (‖r‖ : ℂ)) =
      (Real.exp (-(κ * ‖r‖)) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1; push_cast; ring_nf; simp [Complex.I_sq]
  rw [hexp_eq]
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsqpi : (Real.sqrt Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hrne : (‖r‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr_pos.ne'
  field_simp [hpi, hsqpi, hrne]
  ring

/-! ### Part 4: Integrability of spectral kernels via polar coordinates -/

private lemma integrableOn_poly_exp_Ioi (c : ℝ) (hc : 0 < c) (n : ℕ) :
    IntegrableOn (fun ρ : ℝ => ρ ^ n * Real.exp (-(c * ρ))) (Set.Ioi 0) := by
  have hint_exp : IntegrableOn (fun ρ : ℝ => Real.exp (-((c / 2) * ρ))) (Set.Ioi 0) := by
    have h := integrableOn_exp_mul_Ioi (show -(c / 2) < 0 by linarith) (0 : ℝ)
    exact h.congr_fun (fun ρ _ => by congr 1; ring) measurableSet_Ioi
  have hmeas : AEStronglyMeasurable (fun ρ : ℝ => ρ ^ n * Real.exp (-(c * ρ))) (volume.restrict (Set.Ioi 0)) :=
    (by fun_prop : Continuous fun ρ : ℝ => ρ ^ n * Real.exp (-(c * ρ))).aestronglyMeasurable
  set C : ℝ := (n.factorial : ℝ) / (c / 2) ^ n
  refine Integrable.mono' (hint_exp.const_mul C) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
  have hρ_pos : 0 < ρ := hρ
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hρ_pos.le n) (Real.exp_nonneg _))]
  have hpow : ((c / 2) * ρ) ^ n / (n.factorial : ℝ) ≤ Real.exp ((c / 2) * ρ) :=
    Real.pow_div_factorial_le_exp ((c / 2) * ρ) (by positivity) n
  have hρn : ρ ^ n ≤ C * Real.exp ((c / 2) * ρ) := by
    simp only [C]
    rw [mul_pow] at hpow
    have hfac : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
    have hcp : (0 : ℝ) < (c / 2) ^ n := by positivity
    have h1 : (c / 2) ^ n * ρ ^ n ≤ (n.factorial : ℝ) * Real.exp ((c / 2) * ρ) :=
      ((div_le_iff₀ hfac).mp hpow).trans_eq (mul_comm _ _)
    rw [div_mul_eq_mul_div, le_div_iff₀ hcp]
    linarith
  have hexp_split : Real.exp (-(c * ρ)) = Real.exp (-((c / 2) * ρ)) * Real.exp (-((c / 2) * ρ)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc ρ ^ n * Real.exp (-(c * ρ))
      ≤ (C * Real.exp ((c / 2) * ρ)) * Real.exp (-(c * ρ)) := by gcongr
    _ = C * (Real.exp ((c / 2) * ρ) * Real.exp (-((c / 2) * ρ))) * Real.exp (-((c / 2) * ρ)) := by
        rw [hexp_split]; ring
    _ = C * Real.exp (-((c / 2) * ρ)) := by
        rw [← Real.exp_add]; simp

private lemma integrable_radial_of_Ioi (f : ℝ → ℝ) (hf_nn : ∀ ρ, 0 ≤ f ρ)
    (hfm : Measurable f)
    (hf_int : IntegrableOn (fun ρ : ℝ => ρ * f ρ) (Set.Ioi 0)) :
    Integrable (fun ζ : ℝ × ℝ => f (Real.sqrt (ζ.1 ^ 2 + ζ.2 ^ 2))) volume := by
  have hmeas : AEStronglyMeasurable (fun ζ : ℝ × ℝ => f (Real.sqrt (ζ.1 ^ 2 + ζ.2 ^ 2))) volume :=
    (hfm.comp (Real.continuous_sqrt.measurable.comp (by fun_prop))).aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ζ => hf_nn _)]
  rw [← lintegral_comp_polarCoord_symm]
  have hsymm : ∀ p : ℝ × ℝ, p ∈ polarCoord.target →
      ENNReal.ofReal p.1 * ENNReal.ofReal (f (Real.sqrt ((polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2))) =
      ENNReal.ofReal (p.1 * f p.1) := by
    intro p hp
    have hp1 : 0 < p.1 := hp.1
    have hsq : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
      have hcs := Real.cos_sq_add_sin_sq p.2; nlinarith
    simp only [polarCoord_symm_apply, hsq, Real.sqrt_sq hp1.le]
    rw [ENNReal.ofReal_mul hp1.le]
  have hcongr : (∫⁻ p in polarCoord.target,
      ENNReal.ofReal p.1 * ENNReal.ofReal (f (Real.sqrt ((polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2)))) =
    ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi, ENNReal.ofReal (p.1 * f p.1) := by
    refine setLIntegral_congr_fun polarCoord.open_target.measurableSet fun p hp => ?_
    exact hsymm p hp
  simp only [smul_eq_mul] at hcongr ⊢
  rw [hcongr]
  have hprod : (∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi, ENNReal.ofReal (p.1 * f p.1)) =
      (∫⁻ ρ in Set.Ioi (0 : ℝ), ENNReal.ofReal (ρ * f ρ)) * volume (Set.Ioo (-Real.pi) Real.pi) := by
    rw [← lintegral_indicator (measurableSet_Ioi.prod measurableSet_Ioo)]
    rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl]
    have hmeas_ind : Measurable ((Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
        (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 * f p.1))) :=
      (ENNReal.continuous_ofReal.measurable.comp (measurable_fst.mul (hfm.comp measurable_fst))).indicator
        (measurableSet_Ioi.prod measurableSet_Ioo)
    rw [MeasureTheory.lintegral_prod _ hmeas_ind.aemeasurable]
    have hinner : ∀ ρ : ℝ, (∫⁻ θ : ℝ, (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
        (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 * f p.1)) (ρ, θ)) =
        (Set.Ioi (0 : ℝ)).indicator (fun ρ => ENNReal.ofReal (ρ * f ρ) * volume (Set.Ioo (-Real.pi) Real.pi)) ρ := by
      intro ρ
      by_cases hρ : ρ ∈ Set.Ioi (0 : ℝ)
      · simp only [Set.indicator_of_mem hρ]
        have heq : (fun θ : ℝ => (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
            (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 * f p.1)) (ρ, θ)) =
            (Set.Ioo (-Real.pi) Real.pi).indicator (fun _ => ENNReal.ofReal (ρ * f ρ)) := by
          ext θ; by_cases hθ : θ ∈ Set.Ioo (-Real.pi) Real.pi <;> simp [Set.mem_prod, hρ, hθ]
        rw [heq, lintegral_indicator measurableSet_Ioo, setLIntegral_const]
      · simp only [Set.indicator_of_notMem hρ]
        have heq : (fun θ : ℝ => (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
            (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 * f p.1)) (ρ, θ)) = fun _ => 0 := by
          ext θ; simp [Set.mem_prod, hρ]
        rw [heq, lintegral_zero]
    simp_rw [hinner]
    rw [lintegral_indicator measurableSet_Ioi]
    exact lintegral_mul_const (volume (Set.Ioo (-Real.pi) Real.pi))
      (ENNReal.continuous_ofReal.measurable.comp (measurable_id.mul hfm))
  rw [hprod]
  have h1 : (∫⁻ ρ in Set.Ioi (0 : ℝ), ENNReal.ofReal (ρ * f ρ)) < ⊤ := by
    have hfin := hf_int.2
    rw [hasFiniteIntegral_iff_ofReal] at hfin
    · exact hfin
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
      exact mul_nonneg (le_of_lt hρ) (hf_nn ρ)
  have h2 : volume (Set.Ioo (-Real.pi) Real.pi) < ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
  exact ENNReal.mul_lt_top h1 h2

private lemma integrable_ghat_poly (k : ℂ) (hk : IsCausalWavenumber k) (z : ℝ) (hz : 0 < z) (m : ℕ) :
    Integrable (fun ζ : ℝ × ℝ => (1 + ζ.1 ^ 2 + ζ.2 ^ 2) ^ m * ‖ghat k ζ.1 ζ.2 z‖) volume := by
  let f : ℝ → ℝ := fun ρ => (1 + ρ ^ 2) ^ m * ‖ghat k ρ 0 z‖
  have hf_eq : (fun ζ : ℝ × ℝ => (1 + ζ.1 ^ 2 + ζ.2 ^ 2) ^ m * ‖ghat k ζ.1 ζ.2 z‖) =
      fun ζ => f (Real.sqrt (ζ.1 ^ 2 + ζ.2 ^ 2)) := by
    ext ζ
    simp only [f]
    have hsq : Real.sqrt (ζ.1 ^ 2 + ζ.2 ^ 2) ^ 2 = ζ.1 ^ 2 + ζ.2 ^ 2 := Real.sq_sqrt (by positivity)
    have hsqc : ((Real.sqrt (ζ.1 ^ 2 + ζ.2 ^ 2) : ℝ) : ℂ) ^ 2 + ((0 : ℝ) : ℂ) ^ 2 = (ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 := by
      have : ((Real.sqrt (ζ.1 ^ 2 + ζ.2 ^ 2) ^ 2 : ℝ) : ℂ) = ((ζ.1 ^ 2 + ζ.2 ^ 2 : ℝ) : ℂ) := by rw [hsq]
      simpa using this
    have hβeq : sommerfeldRoot k (Real.sqrt (ζ.1 ^ 2 + ζ.2 ^ 2)) 0 = sommerfeldRoot k ζ.1 ζ.2 := by
      unfold sommerfeldRoot; rw [hsqc]
    rw [hsq, add_assoc]
    simp only [ghat, hβeq]
  rw [hf_eq]
  apply integrable_radial_of_Ioi f (fun ρ => by positivity)
  · have hβm : Measurable (fun ρ : ℝ => sommerfeldRoot k ρ 0) :=
      show Measurable ((fun ζ : ℝ × ℝ => sommerfeldRoot k ζ.1 ζ.2) ∘ fun ρ : ℝ => (ρ, (0 : ℝ))) from
        (measurable_sommerfeldRoot k).comp (measurable_id.prodMk measurable_const)
    have hgm : Measurable (fun ρ : ℝ => ghat k ρ 0 z) := by
      unfold ghat
      exact (Complex.continuous_exp.measurable.comp (hβm.neg.mul measurable_const)).div
        (measurable_const.mul hβm)
    exact (by fun_prop : Measurable fun ρ : ℝ => (1 + ρ ^ 2) ^ m).mul hgm.norm
  · set R : ℝ := 2 * ‖k‖ + 2
    have hR : 0 < R := by positivity
    have hunion : Set.Ioi (0 : ℝ) = Set.Ioo 0 R ∪ Set.Ici R := by
      ext ρ; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioo, Set.mem_Ici]
      constructor
      · intro h; by_cases hlt : ρ < R; exact Or.inl ⟨h, hlt⟩; exact Or.inr (not_lt.mp hlt)
      · rintro (⟨h, _⟩ | h); exact h; linarith
    rw [hunion]
    refine IntegrableOn.union ?_ ?_
    · have hmeas : AEStronglyMeasurable (fun ρ : ℝ => ρ * f ρ) (volume.restrict (Set.Ioo 0 R)) := by
        have hβm : Measurable (fun ρ : ℝ => sommerfeldRoot k ρ 0) :=
          show Measurable ((fun ζ : ℝ × ℝ => sommerfeldRoot k ζ.1 ζ.2) ∘ fun ρ : ℝ => (ρ, (0 : ℝ))) from
            (measurable_sommerfeldRoot k).comp (measurable_id.prodMk measurable_const)
        have hgm : Measurable (fun ρ : ℝ => ghat k ρ 0 z) := by
          unfold ghat
          exact (Complex.continuous_exp.measurable.comp (hβm.neg.mul measurable_const)).div
            (measurable_const.mul hβm)
        exact (measurable_id.mul ((by fun_prop : Measurable fun ρ : ℝ => (1 + ρ ^ 2) ^ m).mul hgm.norm)).aestronglyMeasurable
      by_cases hkim : 0 < k.im
      · set c0 : ℝ := Real.sqrt (2 * k.re * k.im)
        have hc0 : 0 < c0 := Real.sqrt_pos.mpr (by have := hk.1; positivity)
        set M : ℝ := R * (1 + R ^ 2) ^ m / (8 * Real.pi ^ 2 * c0)
        refine Integrable.mono' (integrableOn_const (C := M) (by simp [Real.volume_Ioo])) hmeas ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with ρ ⟨hρ0, hρR⟩
        rw [Real.norm_of_nonneg (mul_nonneg hρ0.le (by positivity))]
        have hβ_lb : c0 ≤ ‖sommerfeldRoot k ρ 0‖ := by
          have h1 : c0 ^ 2 ≤ ‖sommerfeldRoot k ρ 0‖ ^ 2 := by
            rw [Real.sq_sqrt (by have := hk.1; positivity), norm_sommerfeldRoot_sq_eq]
            have him : ((ρ : ℂ) ^ 2 + (0 : ℂ) ^ 2 - k ^ 2).im = -(2 * k.re * k.im) := by
              simp [sq, Complex.mul_im]; ring
            calc 2 * k.re * k.im = |((ρ : ℂ) ^ 2 + (0 : ℂ) ^ 2 - k ^ 2).im| := by
                  rw [him, abs_neg, abs_of_pos (by have := hk.1; positivity)]
              _ ≤ ‖(ρ : ℂ) ^ 2 + (0 : ℂ) ^ 2 - k ^ 2‖ := Complex.abs_im_le_norm _
          exact le_of_sq_le_sq h1 (norm_nonneg _)
        have hghat_le : ‖ghat k ρ 0 z‖ ≤ 1 / (8 * Real.pi ^ 2 * c0) := by
          simp only [ghat, abs_of_pos hz, norm_div, norm_mul, Complex.norm_ofNat, norm_pow,
            Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
          have hexp := norm_exp_neg_sommerfeldRoot_le_one k ρ 0 z hz.le
          have hden1 : 0 < 8 * Real.pi ^ 2 * c0 := by positivity
          exact div_le_div₀ zero_le_one hexp hden1 (by gcongr)
        simp only [f, M]
        calc ρ * ((1 + ρ ^ 2) ^ m * ‖ghat k ρ 0 z‖)
            ≤ R * ((1 + R ^ 2) ^ m * (1 / (8 * Real.pi ^ 2 * c0))) := by gcongr
          _ = R * (1 + R ^ 2) ^ m / (8 * Real.pi ^ 2 * c0) := by ring
      · have hkim0 : k.im = 0 := le_antisymm (not_lt.mp hkim) hk.2
        set k0 : ℝ := k.re
        have hk0_pos : 0 < k0 := hk.1
        have hk_eq : k = (k0 : ℂ) := by apply Complex.ext <;> simp [k0, hkim0]
        set C : ℝ := R * (1 + R ^ 2) ^ m / (8 * Real.pi ^ 2 * Real.sqrt k0)
        have hint_sing : IntegrableOn (fun ρ : ℝ => C * |ρ - k0| ^ (-(1 / 2 : ℝ))) (Set.Ioo 0 R) := by
          apply Integrable.const_mul
          have hk0_lt_R : k0 < R := by
            have : k0 ≤ ‖k‖ := by rw [hk_eq, Complex.norm_real, Real.norm_of_nonneg hk0_pos.le]
            linarith
          have hsub : Set.Ioo (0 : ℝ) R ⊆ Set.Ioc 0 k0 ∪ Set.Ioc k0 R := by
            intro ρ ⟨h0, hR'⟩
            by_cases hle : ρ ≤ k0
            · exact Or.inl ⟨h0, hle⟩
            · exact Or.inr ⟨not_le.mp hle, hR'.le⟩
          refine (IntegrableOn.union ?_ ?_).mono_set hsub
          · have h1 : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) volume 0 k0 :=
              intervalIntegral.intervalIntegrable_rpow' (by norm_num)
            have h2 : IntervalIntegrable (fun ρ : ℝ => (k0 - ρ) ^ (-(1 / 2 : ℝ))) volume 0 k0 := by
              simpa using (h1.comp_sub_left k0).symm
            have h3 : IntegrableOn (fun ρ : ℝ => (k0 - ρ) ^ (-(1 / 2 : ℝ))) (Set.Ioc 0 k0) :=
              (intervalIntegrable_iff_integrableOn_Ioc_of_le hk0_pos.le).mp h2
            refine h3.congr_fun (fun ρ hρ => ?_) measurableSet_Ioc
            rw [abs_of_nonpos (sub_nonpos.mpr hρ.2), neg_sub]
          · have h1 : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) volume 0 (R - k0) :=
              intervalIntegral.intervalIntegrable_rpow' (by norm_num)
            have h2 : IntervalIntegrable (fun ρ : ℝ => (ρ - k0) ^ (-(1 / 2 : ℝ))) volume k0 R := by
              simpa using h1.comp_sub_right k0
            have h3 : IntegrableOn (fun ρ : ℝ => (ρ - k0) ^ (-(1 / 2 : ℝ))) (Set.Ioc k0 R) :=
              (intervalIntegrable_iff_integrableOn_Ioc_of_le hk0_lt_R.le).mp h2
            refine h3.congr_fun (fun ρ hρ => ?_) measurableSet_Ioc
            rw [abs_of_pos (sub_pos.mpr hρ.1)]
        refine Integrable.mono' hint_sing hmeas ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with ρ ⟨hρ0, hρR⟩
        rw [Real.norm_of_nonneg (mul_nonneg hρ0.le (by positivity))]
        by_cases hρk : ρ = k0
        · subst hρk
          have hβ0 : sommerfeldRoot k k0 0 = 0 := by
            unfold sommerfeldRoot; rw [hk_eq]; simp
          simp only [f, ghat, hβ0, mul_zero, div_zero, norm_zero, sub_self, abs_zero]
          positivity
        · have hdiff_pos : 0 < |ρ - k0| := abs_pos.mpr (sub_ne_zero.mpr hρk)
          have hβ_norm : Real.sqrt k0 * Real.sqrt |ρ - k0| ≤ ‖sommerfeldRoot k ρ 0‖ := by
            have hsq : (Real.sqrt k0 * Real.sqrt |ρ - k0|) ^ 2 ≤ ‖sommerfeldRoot k ρ 0‖ ^ 2 := by
              rw [mul_pow, Real.sq_sqrt hk0_pos.le, Real.sq_sqrt (abs_nonneg _),
                norm_sommerfeldRoot_sq_eq, hk_eq]
              have hval : (ρ : ℂ) ^ 2 + ((0 : ℝ) : ℂ) ^ 2 - (k0 : ℂ) ^ 2 = (((ρ - k0) * (ρ + k0) : ℝ) : ℂ) := by
                push_cast; ring
              rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_mul,
                abs_of_pos (show 0 < ρ + k0 by linarith)]
              nlinarith [abs_nonneg (ρ - k0)]
            exact le_of_sq_le_sq hsq (norm_nonneg _)
          have hghat_le : ‖ghat k ρ 0 z‖ ≤ 1 / (8 * Real.pi ^ 2 * (Real.sqrt k0 * Real.sqrt |ρ - k0|)) := by
            simp only [ghat, abs_of_pos hz, norm_div, norm_mul, Complex.norm_ofNat, norm_pow,
              Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
            have hexp := norm_exp_neg_sommerfeldRoot_le_one k ρ 0 z hz.le
            have hden : 0 < 8 * Real.pi ^ 2 * (Real.sqrt k0 * Real.sqrt |ρ - k0|) := by positivity
            exact div_le_div₀ zero_le_one hexp hden (by gcongr)
          have hrpow_eq : (Real.sqrt |ρ - k0|)⁻¹ = |ρ - k0| ^ (-(1 / 2 : ℝ)) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (abs_nonneg _)]
          simp only [f, C]
          calc ρ * ((1 + ρ ^ 2) ^ m * ‖ghat k ρ 0 z‖)
              ≤ R * ((1 + R ^ 2) ^ m * (1 / (8 * Real.pi ^ 2 * (Real.sqrt k0 * Real.sqrt |ρ - k0|)))) := by gcongr
            _ = R * (1 + R ^ 2) ^ m / (8 * Real.pi ^ 2 * Real.sqrt k0) * (Real.sqrt |ρ - k0|)⁻¹ := by
                field_simp [Real.pi_ne_zero, (Real.sqrt_pos.mpr hk0_pos).ne', (Real.sqrt_pos.mpr hdiff_pos).ne']
            _ = R * (1 + R ^ 2) ^ m / (8 * Real.pi ^ 2 * Real.sqrt k0) * |ρ - k0| ^ (-(1 / 2 : ℝ)) := by
                rw [hrpow_eq]
    · have hmeas : AEStronglyMeasurable (fun ρ : ℝ => ρ * f ρ) (volume.restrict (Set.Ici R)) := by
        have hβm : Measurable (fun ρ : ℝ => sommerfeldRoot k ρ 0) :=
          show Measurable ((fun ζ : ℝ × ℝ => sommerfeldRoot k ζ.1 ζ.2) ∘ fun ρ : ℝ => (ρ, (0 : ℝ))) from
            (measurable_sommerfeldRoot k).comp (measurable_id.prodMk measurable_const)
        have hgm : Measurable (fun ρ : ℝ => ghat k ρ 0 z) := by
          unfold ghat
          exact (Complex.continuous_exp.measurable.comp (hβm.neg.mul measurable_const)).div
            (measurable_const.mul hβm)
        exact (measurable_id.mul ((by fun_prop : Measurable fun ρ : ℝ => (1 + ρ ^ 2) ^ m).mul hgm.norm)).aestronglyMeasurable
      have hint_tail : IntegrableOn (fun ρ : ℝ => (2 ^ m / (4 * Real.pi ^ 2)) * (ρ ^ (2 * m) * Real.exp (-((z / 2) * ρ)))) (Set.Ici R) := by
        have h1 := (integrableOn_poly_exp_Ioi (z / 2) (half_pos hz) (2 * m)).const_mul (2 ^ m / (4 * Real.pi ^ 2))
        exact IntegrableOn.mono_set h1 (fun ρ (hρ : R ≤ ρ) => lt_of_lt_of_le hR hρ)
      refine Integrable.mono' hint_tail hmeas ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with ρ hρ
      have hρ_ge : R ≤ ρ := hρ
      have hρ_pos : 0 < ρ := lt_of_lt_of_le hR hρ_ge
      have hρ_ge1 : 1 ≤ ρ := by linarith [norm_nonneg k]
      rw [Real.norm_of_nonneg (mul_nonneg hρ_pos.le (by positivity))]
      have hre_lb : ρ ^ 2 / 4 ≤ ((ρ : ℂ) ^ 2 + ((0 : ℝ) : ℂ) ^ 2 - k ^ 2).re := by
        have hk2_re : (k ^ 2).re ≤ ‖k‖ ^ 2 := by
          calc (k ^ 2).re ≤ ‖k ^ 2‖ := Complex.re_le_norm _
            _ = ‖k‖ ^ 2 := norm_pow k 2
        have hre_eq : ((ρ : ℂ) ^ 2 + ((0 : ℝ) : ℂ) ^ 2 - k ^ 2).re = ρ ^ 2 - (k ^ 2).re := by
          simp [sq]
        rw [hre_eq]
        nlinarith [norm_nonneg k]
      have hβ_re : ρ / 2 ≤ (sommerfeldRoot k ρ 0).re := by
        have h1 := sommerfeldRoot_re_sq_ge k ρ 0
        have h2 : (ρ / 2) ^ 2 ≤ (sommerfeldRoot k ρ 0).re ^ 2 := by nlinarith
        exact le_of_sq_le_sq h2 (sommerfeldRoot_re_nonneg k ρ 0)
      have hβ_norm : ρ / 2 ≤ ‖sommerfeldRoot k ρ 0‖ :=
        hβ_re.trans (Complex.re_le_norm _)
      have hghat_le : ‖ghat k ρ 0 z‖ ≤ Real.exp (-((z / 2) * ρ)) / (4 * Real.pi ^ 2 * ρ) := by
        simp only [ghat, abs_of_pos hz, norm_div, norm_mul, Complex.norm_ofNat, norm_pow,
          Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_exp]
        have hre_exp : (-(sommerfeldRoot k ρ 0) * (z : ℂ)).re = -(sommerfeldRoot k ρ 0).re * z := by simp
        rw [hre_exp]
        have hexp_le : Real.exp (-(sommerfeldRoot k ρ 0).re * z) ≤ Real.exp (-((z / 2) * ρ)) :=
          Real.exp_le_exp.mpr (by nlinarith)
        have hden_le : 4 * Real.pi ^ 2 * ρ ≤ 8 * Real.pi ^ 2 * ‖sommerfeldRoot k ρ 0‖ := by
          have : 0 < Real.pi ^ 2 := by positivity
          nlinarith
        exact div_le_div₀ (Real.exp_nonneg _) hexp_le (by positivity) hden_le
      have h1ρ : (1 + ρ ^ 2) ^ m ≤ 2 ^ m * ρ ^ (2 * m) := by
        rw [pow_mul, ← mul_pow]
        exact pow_le_pow_left₀ (by positivity) (by nlinarith) m
      simp only [f]
      calc ρ * ((1 + ρ ^ 2) ^ m * ‖ghat k ρ 0 z‖)
          ≤ ρ * ((2 ^ m * ρ ^ (2 * m)) * (Real.exp (-((z / 2) * ρ)) / (4 * Real.pi ^ 2 * ρ))) := by gcongr
        _ = (2 ^ m / (4 * Real.pi ^ 2)) * (ρ ^ (2 * m) * Real.exp (-((z / 2) * ρ))) := by
            field_simp [hρ_pos.ne', Real.pi_ne_zero]

/-! ### Part 5: Analytic continuation to the upper half-plane `{k | 0 < k.im}` -/

private lemma slitPlane_of_im_pos {k : ℂ} (hk : 0 < k.im) (ξ η : ℝ) :
    (ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hre : k.re = 0
  · left
    have : ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2).re = ξ ^ 2 + η ^ 2 + k.im ^ 2 := by
      simp [sq, Complex.mul_re, hre]
    rw [this]; positivity
  · right
    have : ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2).im = -(2 * k.re * k.im) := by
      simp [sq, Complex.mul_im]; ring
    rw [this]
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero two_ne_zero hre) hk.ne')

private lemma sommerfeldRoot_eq_cpow_of_im_pos {k : ℂ} (hk : 0 < k.im) (ξ η : ℝ) :
    sommerfeldRoot k ξ η = ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2) ^ (1 / 2 : ℂ) := by
  unfold sommerfeldRoot
  have hs := slitPlane_of_im_pos hk ξ η
  rw [Complex.mem_slitPlane_iff] at hs
  have hnot : ¬(((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2).im = 0 ∧
      ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2).re < 0) := by
    rintro ⟨him, hre⟩
    rcases hs with hpos | hne
    · linarith
    · exact hne him
  exact if_neg hnot

private lemma norm_sommerfeldRoot_ge_of_im_ge {k : ℂ} {δ : ℝ} (hδ : 0 < δ) (hkim : δ ≤ k.im)
    (ξ η : ℝ) : δ / 2 ≤ ‖sommerfeldRoot k ξ η‖ := by
  have hsq : (δ / 2) ^ 2 ≤ ‖sommerfeldRoot k ξ η‖ ^ 2 := by
    rw [norm_sommerfeldRoot_sq_eq]
    by_cases hre : δ / 2 ≤ |k.re|
    · have him : ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2).im = -(2 * k.re * k.im) := by
        simp [sq, Complex.mul_im]; ring
      calc (δ / 2) ^ 2 ≤ 2 * |k.re| * k.im := by nlinarith
        _ = |((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2).im| := by
            rw [him, abs_neg, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
              abs_of_pos (lt_of_lt_of_le hδ hkim)]
        _ ≤ ‖(ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2‖ := Complex.abs_im_le_norm _
    · push Not at hre
      have hre_eq : ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2).re = ξ ^ 2 + η ^ 2 + k.im ^ 2 - k.re ^ 2 := by
        simp [sq, Complex.mul_re]; ring
      have hk_sq : k.re ^ 2 ≤ (δ / 2) ^ 2 := by
        rw [← sq_abs]; nlinarith [abs_nonneg k.re]
      calc (δ / 2) ^ 2 ≤ ξ ^ 2 + η ^ 2 + k.im ^ 2 - k.re ^ 2 := by
            nlinarith [sq_nonneg ξ, sq_nonneg η]
        _ = ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2).re := hre_eq.symm
        _ ≤ ‖(ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2‖ := Complex.re_le_norm _
  exact le_of_sq_le_sq hsq (norm_nonneg _)

private lemma hasDerivAt_ghat_of_im_pos {k : ℂ} (hk : 0 < k.im) (ξ η z : ℝ) (hz : 0 < z) :
    HasDerivAt (fun w : ℂ => ghat w ξ η z)
      (Complex.exp (-(sommerfeldRoot k ξ η) * z) * k * (z * sommerfeldRoot k ξ η + 1) /
        (8 * Real.pi ^ 2 * sommerfeldRoot k ξ η ^ 3)) k := by
  have hs := slitPlane_of_im_pos hk ξ η
  set u : ℂ := (ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2
  have hu_ne : u ≠ 0 := Complex.slitPlane_ne_zero hs
  have hβ_ne : sommerfeldRoot k ξ η ≠ 0 := by
    have h := norm_sommerfeldRoot_ge_of_im_ge hk le_rfl ξ η
    intro h0; rw [h0, norm_zero] at h; linarith
  have hβ_deriv : HasDerivAt (fun w : ℂ => sommerfeldRoot w ξ η) (-k / sommerfeldRoot k ξ η) k := by
    have hu_deriv : HasDerivAt (fun w : ℂ => (ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - w ^ 2) (-2 * k) k := by
      have h1 := (hasDerivAt_const k ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2)).sub (hasDerivAt_pow 2 k)
      have hfun : ((fun _ : ℂ => (ξ : ℂ) ^ 2 + (η : ℂ) ^ 2) - fun w : ℂ => w ^ 2) =
          fun w : ℂ => (ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - w ^ 2 := rfl
      rw [hfun] at h1
      have hval : (0 : ℂ) - ((2 : ℕ) : ℂ) * k ^ (2 - 1) = -2 * k := by norm_num
      rw [hval] at h1
      exact h1
    have hlog_deriv : HasDerivAt (fun w : ℂ => Complex.log ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - w ^ 2))
        (u⁻¹ * (-2 * k)) k :=
      show HasDerivAt (Complex.log ∘ fun w : ℂ => (ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - w ^ 2) (u⁻¹ * (-2 * k)) k from
        (Complex.hasDerivAt_log hs).comp k hu_deriv
    have hexp_deriv : HasDerivAt
        (fun w : ℂ => Complex.exp (Complex.log ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - w ^ 2) * (1 / 2 : ℂ)))
        (Complex.exp (Complex.log u * (1 / 2 : ℂ)) * (u⁻¹ * (-2 * k) * (1 / 2 : ℂ))) k :=
      (Complex.hasDerivAt_exp _).comp k (hlog_deriv.mul_const (1 / 2 : ℂ))
    have hev : (fun w : ℂ => sommerfeldRoot w ξ η) =ᶠ[𝓝 k]
        fun w => Complex.exp (Complex.log ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - w ^ 2) * (1 / 2 : ℂ)) := by
      have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
      filter_upwards [hopen.mem_nhds hk] with w hw
      rw [sommerfeldRoot_eq_cpow_of_im_pos hw,
        Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero (slitPlane_of_im_pos hw ξ η))]
    have hval : Complex.exp (Complex.log u * (1 / 2 : ℂ)) * (u⁻¹ * (-2 * k) * (1 / 2 : ℂ)) =
        -k / sommerfeldRoot k ξ η := by
      have hβ_eq : Complex.exp (Complex.log u * (1 / 2 : ℂ)) = sommerfeldRoot k ξ η := by
        rw [sommerfeldRoot_eq_cpow_of_im_pos hk, Complex.cpow_def_of_ne_zero hu_ne]
      have hu_eq : u = sommerfeldRoot k ξ η ^ 2 := (sommerfeldRoot_sq k ξ η).symm
      rw [hβ_eq, hu_eq]
      field_simp [hβ_ne]
    rw [hval] at hexp_deriv
    exact hexp_deriv.congr_of_eventuallyEq hev
  have hnum_deriv : HasDerivAt (fun w : ℂ => Complex.exp (-(sommerfeldRoot w ξ η) * (z : ℂ)))
      (Complex.exp (-(sommerfeldRoot k ξ η) * (z : ℂ)) * (-(-k / sommerfeldRoot k ξ η) * (z : ℂ))) k :=
    (Complex.hasDerivAt_exp _).comp k (hβ_deriv.neg.mul_const (z : ℂ))
  have hden_deriv : HasDerivAt (fun w : ℂ => 8 * (Real.pi : ℂ) ^ 2 * sommerfeldRoot w ξ η)
      (8 * (Real.pi : ℂ) ^ 2 * (-k / sommerfeldRoot k ξ η)) k :=
    hβ_deriv.const_mul (8 * (Real.pi : ℂ) ^ 2)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hden_ne : 8 * (Real.pi : ℂ) ^ 2 * sommerfeldRoot k ξ η ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hpi)) hβ_ne
  have hdiv := hnum_deriv.div hden_deriv hden_ne
  have hfun : ((fun w : ℂ => Complex.exp (-(sommerfeldRoot w ξ η) * (z : ℂ))) /
      (fun w : ℂ => 8 * (Real.pi : ℂ) ^ 2 * sommerfeldRoot w ξ η)) = fun w => ghat w ξ η z := by
    ext w; simp [ghat, abs_of_pos hz]
  rw [hfun] at hdiv
  have hderiv_eq :
      (Complex.exp (-(sommerfeldRoot k ξ η) * (z : ℂ)) * (-(-k / sommerfeldRoot k ξ η) * (z : ℂ)) *
          (8 * (Real.pi : ℂ) ^ 2 * sommerfeldRoot k ξ η) -
        Complex.exp (-(sommerfeldRoot k ξ η) * (z : ℂ)) *
          (8 * (Real.pi : ℂ) ^ 2 * (-k / sommerfeldRoot k ξ η))) /
        (8 * (Real.pi : ℂ) ^ 2 * sommerfeldRoot k ξ η) ^ 2 =
      Complex.exp (-(sommerfeldRoot k ξ η) * (z : ℂ)) * k * ((z : ℂ) * sommerfeldRoot k ξ η + 1) /
        (8 * (Real.pi : ℂ) ^ 2 * sommerfeldRoot k ξ η ^ 3) := by
    field_simp [hpi, hβ_ne]; ring
  rw [hderiv_eq] at hdiv
  exact hdiv

private lemma integrable_ghat_pw_of_im_pos (k₀ : ℂ) (hk₀ : 0 < k₀.im) (z x y : ℝ) (hz : 0 < z) :
    Integrable (fun ζ : ℝ × ℝ => ghat k₀ ζ.1 ζ.2 z * planeWave ζ.1 ζ.2 x y) volume := by
  set δ : ℝ := k₀.im / 2 with hδ_def
  have hδ : 0 < δ := half_pos hk₀
  set M : ℝ := ‖k₀‖ + δ
  have hM : 0 < M := by positivity
  set R : ℝ := 2 * M + 2
  have hR : 0 < R := by positivity
  let b0_r : ℝ → ℝ := fun ρ =>
    if ρ < R then 1 / (8 * Real.pi ^ 2 * (δ / 2)) else Real.exp (-((z / 2) * ρ)) / (4 * Real.pi ^ 2 * ρ)
  have hb0_int : Integrable (fun ζ : ℝ × ℝ => b0_r (Real.sqrt (ζ.1 ^ 2 + ζ.2 ^ 2))) volume := by
    apply integrable_radial_of_Ioi b0_r
    · intro ρ; dsimp only [b0_r]; split_ifs with h
      · positivity
      · have hρ0 : 0 ≤ ρ := by linarith [not_lt.mp h]
        positivity
    · exact Measurable.ite measurableSet_Iio measurable_const (by fun_prop)
    · have hunion : Set.Ioi (0 : ℝ) = Set.Ioo 0 R ∪ Set.Ici R := by
        ext ρ; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioo, Set.mem_Ici]
        constructor
        · intro h; by_cases hlt : ρ < R; exact Or.inl ⟨h, hlt⟩; exact Or.inr (not_lt.mp hlt)
        · rintro (⟨h, _⟩ | h); exact h; linarith
      rw [hunion]
      refine IntegrableOn.union ?_ ?_
      · have h1 : IntegrableOn (fun ρ : ℝ => ρ * (1 / (8 * Real.pi ^ 2 * (δ / 2)))) (Set.Ioo 0 R) :=
          (continuous_id.mul continuous_const).continuousOn.integrableOn_compact isCompact_Icc |>.mono_set Set.Ioo_subset_Icc_self
        exact h1.congr_fun (fun ρ hρ => by simp [b0_r, hρ.2]) measurableSet_Ioo
      · have h1 : IntegrableOn (fun ρ : ℝ => (1 / (4 * Real.pi ^ 2)) * (ρ ^ 0 * Real.exp (-((z / 2) * ρ)))) (Set.Ici R) :=
          IntegrableOn.mono_set ((integrableOn_poly_exp_Ioi (z / 2) (half_pos hz) 0).const_mul (1 / (4 * Real.pi ^ 2)))
            (fun ρ (hρ : R ≤ ρ) => lt_of_lt_of_le hR hρ)
        refine h1.congr_fun (fun ρ hρ => ?_) measurableSet_Ici
        have hρ' : R ≤ ρ := hρ
        have hρ_pos : 0 < ρ := lt_of_lt_of_le hR hρ'
        simp only [b0_r, if_neg (not_lt.mpr hρ'), pow_zero, one_mul]
        field_simp [hρ_pos.ne', Real.pi_ne_zero]
  have hmeas : AEStronglyMeasurable (fun ζ : ℝ × ℝ => ghat k₀ ζ.1 ζ.2 z * planeWave ζ.1 ζ.2 x y) volume := by
    have hpw : Measurable (fun ζ : ℝ × ℝ => planeWave ζ.1 ζ.2 x y) := by unfold planeWave; fun_prop
    exact ((measurable_ghat k₀ z).mul hpw).aestronglyMeasurable
  refine Integrable.mono' hb0_int hmeas (Eventually.of_forall fun ζ => ?_)
  simp only [norm_mul, norm_planeWave, mul_one]
  set ρ : ℝ := Real.sqrt (ζ.1 ^ 2 + ζ.2 ^ 2)
  have hρ_sq : ρ ^ 2 = ζ.1 ^ 2 + ζ.2 ^ 2 := Real.sq_sqrt (by positivity)
  simp only [ghat, abs_of_pos hz, norm_div, norm_mul, Complex.norm_ofNat, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, b0_r]
  split_ifs with hlt
  · have hβ_lb := norm_sommerfeldRoot_ge_of_im_ge hδ (by linarith [hδ_def] : δ ≤ k₀.im) ζ.1 ζ.2
    have hexp := norm_exp_neg_sommerfeldRoot_le_one k₀ ζ.1 ζ.2 z hz.le
    exact div_le_div₀ zero_le_one hexp (by positivity) (by gcongr)
  · have hρ_ge : R ≤ ρ := not_lt.mp hlt
    have hρ_pos : 0 < ρ := lt_of_lt_of_le hR hρ_ge
    have hre_lb : ρ ^ 2 / 4 ≤ ((ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - k₀ ^ 2).re := by
      have hk2_re : (k₀ ^ 2).re ≤ ‖k₀‖ ^ 2 := (Complex.re_le_norm _).trans (by rw [norm_pow])
      have hre_eq : ((ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - k₀ ^ 2).re = ρ ^ 2 - (k₀ ^ 2).re := by
        simp [sq, hρ_sq]
      rw [hre_eq]; nlinarith [norm_nonneg k₀]
    have hβ_re : ρ / 2 ≤ (sommerfeldRoot k₀ ζ.1 ζ.2).re :=
      le_of_sq_le_sq (by nlinarith [sommerfeldRoot_re_sq_ge k₀ ζ.1 ζ.2]) (sommerfeldRoot_re_nonneg k₀ ζ.1 ζ.2)
    have hβ_norm : ρ / 2 ≤ ‖sommerfeldRoot k₀ ζ.1 ζ.2‖ := hβ_re.trans (Complex.re_le_norm _)
    rw [Complex.norm_exp]
    have hre_exp : (-(sommerfeldRoot k₀ ζ.1 ζ.2) * (z : ℂ)).re = -(sommerfeldRoot k₀ ζ.1 ζ.2).re * z := by simp
    rw [hre_exp]
    have hexp_le : Real.exp (-(sommerfeldRoot k₀ ζ.1 ζ.2).re * z) ≤ Real.exp (-((z / 2) * ρ)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hden_le : 4 * Real.pi ^ 2 * ρ ≤ 8 * Real.pi ^ 2 * ‖sommerfeldRoot k₀ ζ.1 ζ.2‖ := by
      have : 0 < Real.pi ^ 2 := by positivity
      nlinarith
    exact div_le_div₀ (Real.exp_nonneg _) hexp_le (by positivity) hden_le

private lemma differentiableAt_sommerfeld_of_im_pos (k₀ : ℂ) (hk₀ : 0 < k₀.im) (z x y : ℝ) (hz : 0 < z) :
    DifferentiableAt ℂ (fun w : ℂ => ∫ ζ : ℝ × ℝ, ghat w ζ.1 ζ.2 z * planeWave ζ.1 ζ.2 x y) k₀ := by
  set δ : ℝ := k₀.im / 2 with hδ_def
  have hδ : 0 < δ := half_pos hk₀
  set M : ℝ := ‖k₀‖ + δ
  have hM : 0 < M := by positivity
  set R : ℝ := 2 * M + 2
  have hR : 0 < R := by positivity
  have hball_im : ∀ w ∈ Metric.ball k₀ δ, δ ≤ w.im := by
    intro w hw
    have hd : ‖w - k₀‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have him : |w.im - k₀.im| ≤ ‖w - k₀‖ := Complex.abs_im_le_norm (w - k₀)
    linarith [(abs_le.mp (him.trans hd.le)).1, hδ_def]
  have hball_norm : ∀ w ∈ Metric.ball k₀ δ, ‖w‖ ≤ M := by
    intro w hw
    have hd : ‖w - k₀‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have htri : ‖w‖ - ‖k₀‖ ≤ ‖w - k₀‖ := norm_sub_norm_le w k₀
    linarith
  let F : ℂ → ℝ × ℝ → ℂ := fun w ζ => ghat w ζ.1 ζ.2 z * planeWave ζ.1 ζ.2 x y
  let F' : ℂ → ℝ × ℝ → ℂ := fun w ζ =>
    (Complex.exp (-(sommerfeldRoot w ζ.1 ζ.2) * z) * w * (z * sommerfeldRoot w ζ.1 ζ.2 + 1) /
      (8 * Real.pi ^ 2 * sommerfeldRoot w ζ.1 ζ.2 ^ 3)) * planeWave ζ.1 ζ.2 x y
  let C₁ : ℝ := M * (z * (1 + M) * Real.sqrt (1 + R ^ 2) + 1) / (8 * Real.pi ^ 2 * (δ / 2) ^ 3)
  let C₂ : ℝ := M * (z * (1 + M) * 2 + 1) / (Real.pi ^ 2)
  let bound_r : ℝ → ℝ := fun ρ => if ρ < R then C₁ else C₂ * Real.exp (-((z / 2) * ρ))
  let bound : ℝ × ℝ → ℝ := fun ζ => bound_r (Real.sqrt (ζ.1 ^ 2 + ζ.2 ^ 2))
  have hbound_int : Integrable bound volume := by
    apply integrable_radial_of_Ioi bound_r
    · intro ρ; dsimp only [bound_r]; split_ifs <;> positivity
    · exact Measurable.ite measurableSet_Iio measurable_const (by fun_prop)
    · have hunion : Set.Ioi (0 : ℝ) = Set.Ioo 0 R ∪ Set.Ici R := by
        ext ρ; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioo, Set.mem_Ici]
        constructor
        · intro h; by_cases hlt : ρ < R; exact Or.inl ⟨h, hlt⟩; exact Or.inr (not_lt.mp hlt)
        · rintro (⟨h, _⟩ | h); exact h; linarith
      rw [hunion]
      refine IntegrableOn.union ?_ ?_
      · have h1 : IntegrableOn (fun ρ : ℝ => ρ * C₁) (Set.Ioo 0 R) :=
          (continuous_id.mul continuous_const).continuousOn.integrableOn_compact isCompact_Icc |>.mono_set Set.Ioo_subset_Icc_self
        exact h1.congr_fun (fun ρ hρ => by simp [bound_r, hρ.2]) measurableSet_Ioo
      · have h1 : IntegrableOn (fun ρ : ℝ => C₂ * (ρ ^ 1 * Real.exp (-((z / 2) * ρ)))) (Set.Ici R) :=
          IntegrableOn.mono_set ((integrableOn_poly_exp_Ioi (z / 2) (half_pos hz) 1).const_mul C₂)
            (fun ρ (hρ : R ≤ ρ) => lt_of_lt_of_le hR hρ)
        refine h1.congr_fun (fun ρ hρ => ?_) measurableSet_Ici
        have hρ' : R ≤ ρ := hρ
        simp only [bound_r, if_neg (not_lt.mpr hρ'), pow_one]; ring
  have hF_meas : ∀ w : ℂ, AEStronglyMeasurable (F w) volume := by
    intro w
    have hpw : Measurable (fun ζ : ℝ × ℝ => planeWave ζ.1 ζ.2 x y) := by unfold planeWave; fun_prop
    exact ((measurable_ghat w z).mul hpw).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable (F' k₀) volume := by
    have hβ := measurable_sommerfeldRoot k₀
    have hpw : Measurable (fun ζ : ℝ × ℝ => planeWave ζ.1 ζ.2 x y) := by unfold planeWave; fun_prop
    have hnum : Measurable (fun ζ : ℝ × ℝ =>
        Complex.exp (-(sommerfeldRoot k₀ ζ.1 ζ.2) * z) * k₀ * (z * sommerfeldRoot k₀ ζ.1 ζ.2 + 1)) :=
      ((Complex.continuous_exp.measurable.comp (hβ.neg.mul measurable_const)).mul measurable_const).mul
        ((measurable_const.mul hβ).add measurable_const)
    have hden : Measurable (fun ζ : ℝ × ℝ => 8 * (Real.pi : ℂ) ^ 2 * sommerfeldRoot k₀ ζ.1 ζ.2 ^ 3) :=
      measurable_const.mul (hβ.pow_const 3)
    exact ((hnum.div hden).mul hpw).aestronglyMeasurable
  have hF_int : Integrable (F k₀) volume := integrable_ghat_pw_of_im_pos k₀ hk₀ z x y hz
  have hF'_bound : ∀ ζ : ℝ × ℝ, ∀ w ∈ Metric.ball k₀ δ, ‖F' w ζ‖ ≤ bound ζ := by
    intro ζ w hw
    have hw_im := hball_im w hw
    have hw_norm := hball_norm w hw
    set ρ : ℝ := Real.sqrt (ζ.1 ^ 2 + ζ.2 ^ 2)
    have hρ_sq : ρ ^ 2 = ζ.1 ^ 2 + ζ.2 ^ 2 := Real.sq_sqrt (by positivity)
    have hρ_nn : 0 ≤ ρ := Real.sqrt_nonneg _
    simp only [F', bound, bound_r, norm_mul, norm_div, norm_planeWave, mul_one,
      Complex.norm_ofNat, norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have hβ_ub : ‖sommerfeldRoot w ζ.1 ζ.2‖ ≤ (1 + M) * Real.sqrt (1 + ρ ^ 2) := by
      have h1 := norm_sommerfeldRoot_le w ζ.1 ζ.2
      have h2 : 1 + ζ.1 ^ 2 + ζ.2 ^ 2 = 1 + ρ ^ 2 := by linarith
      rw [h2] at h1
      exact h1.trans (by gcongr)
    have hnum_le : ‖(z : ℂ) * sommerfeldRoot w ζ.1 ζ.2 + 1‖ ≤ z * (1 + M) * Real.sqrt (1 + ρ ^ 2) + 1 := by
      calc ‖(z : ℂ) * sommerfeldRoot w ζ.1 ζ.2 + 1‖
          ≤ ‖(z : ℂ) * sommerfeldRoot w ζ.1 ζ.2‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = z * ‖sommerfeldRoot w ζ.1 ζ.2‖ + 1 := by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hz.le, norm_one]
        _ ≤ z * ((1 + M) * Real.sqrt (1 + ρ ^ 2)) + 1 := by gcongr
        _ = z * (1 + M) * Real.sqrt (1 + ρ ^ 2) + 1 := by ring
    split_ifs with hlt
    · have hβ_lb := norm_sommerfeldRoot_ge_of_im_ge hδ hw_im ζ.1 ζ.2
      have hexp := norm_exp_neg_sommerfeldRoot_le_one w ζ.1 ζ.2 z hz.le
      have hsqrt_le : Real.sqrt (1 + ρ ^ 2) ≤ Real.sqrt (1 + R ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
      simp only [C₁]
      have hnum2 : ‖Complex.exp (-(sommerfeldRoot w ζ.1 ζ.2) * (z : ℂ))‖ * ‖w‖ *
          ‖(z : ℂ) * sommerfeldRoot w ζ.1 ζ.2 + 1‖ ≤
          M * (z * (1 + M) * Real.sqrt (1 + R ^ 2) + 1) := by
        calc ‖Complex.exp (-(sommerfeldRoot w ζ.1 ζ.2) * (z : ℂ))‖ * ‖w‖ *
              ‖(z : ℂ) * sommerfeldRoot w ζ.1 ζ.2 + 1‖
            ≤ 1 * M * (z * (1 + M) * Real.sqrt (1 + R ^ 2) + 1) := by
              have h3 : ‖(z : ℂ) * sommerfeldRoot w ζ.1 ζ.2 + 1‖ ≤ z * (1 + M) * Real.sqrt (1 + R ^ 2) + 1 :=
                hnum_le.trans (by gcongr)
              gcongr
          _ = M * (z * (1 + M) * Real.sqrt (1 + R ^ 2) + 1) := by ring
      exact div_le_div₀ (by positivity) hnum2 (by positivity) (by gcongr)
    · have hρ_ge : R ≤ ρ := not_lt.mp hlt
      have hρ_pos : 0 < ρ := lt_of_lt_of_le hR hρ_ge
      have hρ_ge1 : 1 ≤ ρ := by linarith
      have hre_lb : ρ ^ 2 / 4 ≤ ((ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - w ^ 2).re := by
        have hw2_re : (w ^ 2).re ≤ ‖w‖ ^ 2 := (Complex.re_le_norm _).trans (by rw [norm_pow])
        have hre_eq : ((ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - w ^ 2).re = ρ ^ 2 - (w ^ 2).re := by
          simp [sq, hρ_sq]
        rw [hre_eq]; nlinarith [norm_nonneg w]
      have hβ_re : ρ / 2 ≤ (sommerfeldRoot w ζ.1 ζ.2).re :=
        le_of_sq_le_sq (by nlinarith [sommerfeldRoot_re_sq_ge w ζ.1 ζ.2]) (sommerfeldRoot_re_nonneg w ζ.1 ζ.2)
      have hβ_norm : ρ / 2 ≤ ‖sommerfeldRoot w ζ.1 ζ.2‖ := hβ_re.trans (Complex.re_le_norm _)
      have hsqrt_le : Real.sqrt (1 + ρ ^ 2) ≤ 2 * ρ :=
        Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
      have hnum3 : ‖(z : ℂ) * sommerfeldRoot w ζ.1 ζ.2 + 1‖ ≤ (z * (1 + M) * 2 + 1) * ρ := by
        calc ‖(z : ℂ) * sommerfeldRoot w ζ.1 ζ.2 + 1‖
            ≤ z * (1 + M) * (2 * ρ) + 1 := hnum_le.trans (by gcongr)
          _ ≤ z * (1 + M) * (2 * ρ) + ρ := by linarith
          _ = (z * (1 + M) * 2 + 1) * ρ := by ring
      have hexp_le : ‖Complex.exp (-(sommerfeldRoot w ζ.1 ζ.2) * (z : ℂ))‖ ≤ Real.exp (-((z / 2) * ρ)) := by
        rw [Complex.norm_exp]
        have hre_exp : (-(sommerfeldRoot w ζ.1 ζ.2) * (z : ℂ)).re = -(sommerfeldRoot w ζ.1 ζ.2).re * z := by simp
        rw [hre_exp]; exact Real.exp_le_exp.mpr (by nlinarith)
      have hden_le : Real.pi ^ 2 * ρ ^ 3 ≤ 8 * Real.pi ^ 2 * ‖sommerfeldRoot w ζ.1 ζ.2‖ ^ 3 := by
        have h1 : (ρ / 2) ^ 3 ≤ ‖sommerfeldRoot w ζ.1 ζ.2‖ ^ 3 := pow_le_pow_left₀ (by positivity) hβ_norm 3
        have h2 : 8 * (ρ / 2) ^ 3 = ρ ^ 3 := by ring
        have hpi2 : 0 < Real.pi ^ 2 := by positivity
        nlinarith
      simp only [C₂]
      calc ‖Complex.exp (-(sommerfeldRoot w ζ.1 ζ.2) * (z : ℂ))‖ * ‖w‖ *
            ‖(z : ℂ) * sommerfeldRoot w ζ.1 ζ.2 + 1‖ / (8 * Real.pi ^ 2 * ‖sommerfeldRoot w ζ.1 ζ.2‖ ^ 3)
          ≤ (Real.exp (-((z / 2) * ρ)) * M * ((z * (1 + M) * 2 + 1) * ρ)) / (Real.pi ^ 2 * ρ ^ 3) :=
            div_le_div₀ (by positivity) (by gcongr) (by positivity) hden_le
        _ = M * (z * (1 + M) * 2 + 1) / Real.pi ^ 2 * Real.exp (-((z / 2) * ρ)) / ρ ^ 2 := by
            field_simp [Real.pi_ne_zero, hρ_pos.ne']
        _ ≤ M * (z * (1 + M) * 2 + 1) / Real.pi ^ 2 * Real.exp (-((z / 2) * ρ)) := by
            exact div_le_self (by positivity) (by nlinarith)
  have hF_diff : ∀ᵐ ζ : ℝ × ℝ ∂volume, ∀ w ∈ Metric.ball k₀ δ, HasDerivAt (fun w => F w ζ) (F' w ζ) w :=
    Eventually.of_forall fun ζ w hw =>
      (hasDerivAt_ghat_of_im_pos (lt_of_lt_of_le hδ (hball_im w hw)) ζ.1 ζ.2 z hz).mul_const
        (planeWave ζ.1 ζ.2 x y)
  have hhas : HasDerivAt (fun w => ∫ ζ : ℝ × ℝ, F w ζ) (∫ ζ : ℝ × ℝ, F' k₀ ζ) k₀ :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') (bound := bound)
      (s := Metric.ball k₀ δ) (Metric.ball_mem_nhds k₀ hδ)
      (Eventually.of_forall hF_meas) hF_int hF'_meas
      (Eventually.of_forall hF'_bound) hbound_int hF_diff).2
  exact hhas.differentiableAt

private lemma sommerfeld_upperHalfPlane (k : ℂ) (hk : 0 < k.im) (r : Space) (hr : 0 < r 2) :
    greenFn k r =
      ∫ ζ : ℝ × ℝ, ghat k ζ.1 ζ.2 (r 2) * planeWave ζ.1 ζ.2 (r 0) (r 1) := by
  set z : ℝ := r 2
  have hz : 0 < z := hr
  let U : Set ℂ := {w : ℂ | 0 < w.im}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hU_preconn : IsPreconnected U := by
    have hconv : Convex ℝ U := by
      intro x hx y hy a b ha hb hab
      change 0 < (a • x + b • y).im
      simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero]
      rcases ha.eq_or_lt with rfl | ha'
      · have hb1 : b = 1 := by linarith
        rw [hb1]; simpa using (show 0 < y.im from hy)
      · nlinarith [mul_pos ha' (show 0 < x.im from hx), mul_nonneg hb (le_of_lt (show 0 < y.im from hy))]
    exact hconv.isPreconnected
  let G : ℂ → ℂ := fun w => ∫ ζ : ℝ × ℝ, ghat w ζ.1 ζ.2 z * planeWave ζ.1 ζ.2 (r 0) (r 1)
  have hG_diff : DifferentiableOn ℂ G U :=
    fun k₀ hk₀ => (differentiableAt_sommerfeld_of_im_pos k₀ hk₀ z (r 0) (r 1) hz).differentiableWithinAt
  have hG_ana : AnalyticOnNhd ℂ G U := hG_diff.analyticOnNhd hU_open
  have hg_ana : AnalyticOnNhd ℂ (fun w : ℂ => greenFn w r) U := by
    have hg_diff : DifferentiableOn ℂ (fun w : ℂ => greenFn w r) U := by
      intro w _; unfold greenFn; exact (((differentiableAt_id.const_mul Complex.I).mul_const _).cexp.div_const _).differentiableWithinAt
    exact hg_diff.analyticOnNhd hU_open
  have hI_mem : Complex.I ∈ U := by simp [U]
  have hfreq : ∃ᶠ w in 𝓝[≠] Complex.I, greenFn w r = G w := by
    rw [frequently_nhdsWithin_iff, Metric.nhds_basis_ball.frequently_iff]
    intro ε hε
    refine ⟨Complex.I * ((1 + ε / 2 : ℝ) : ℂ), ?_, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      have hsub : Complex.I * ((1 + ε / 2 : ℝ) : ℂ) - Complex.I = Complex.I * ((ε / 2 : ℝ) : ℂ) := by
        push_cast; ring
      rw [hsub, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      linarith
    · exact sommerfeld_pure_imag (1 + ε / 2) (by linarith) r hr
    · intro h
      have him := congrArg Complex.im h
      simp at him; linarith
  exact hg_ana.eqOn_of_preconnected_of_frequently_eq hG_ana hU_preconn hI_mem hfreq hk

/-! ### Part 6: Limit to the real axis (`k.im = 0`, `0 < k.re`) -/

private lemma measure_circle_zero (R : ℝ) (hR : 0 < R) :
    volume ({ζ : ℝ × ℝ | ζ.1 ^ 2 + ζ.2 ^ 2 = R ^ 2}) = 0 := by
  have hmeas : MeasurableSet ({ζ : ℝ × ℝ | ζ.1 ^ 2 + ζ.2 ^ 2 = R ^ 2}) :=
    (by fun_prop : Continuous fun ζ : ℝ × ℝ => ζ.1 ^ 2 + ζ.2 ^ 2).measurable (measurableSet_singleton (R ^ 2))
  rw [← lintegral_indicator_one hmeas, ← lintegral_comp_polarCoord_symm]
  have hzero : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • ({ζ : ℝ × ℝ | ζ.1 ^ 2 + ζ.2 ^ 2 = R ^ 2}.indicator (1 : ℝ × ℝ → ENNReal) (polarCoord.symm p)) =
      (({p : ℝ × ℝ | p.1 = R}).indicator (fun p => ENNReal.ofReal p.1) p) := by
    intro p hp
    have hp1 : 0 < p.1 := hp.1
    have hsq : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
      have hcs := Real.cos_sq_add_sin_sq p.2; nlinarith
    have hiff : p.1 ^ 2 = R ^ 2 ↔ p.1 = R := by
      constructor
      · intro h; nlinarith
      · intro h; rw [h]
    by_cases h : p.1 = R
    · have hmem : polarCoord.symm p ∈ {ζ : ℝ × ℝ | ζ.1 ^ 2 + ζ.2 ^ 2 = R ^ 2} := by
        change (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = R ^ 2
        rw [hsq, hiff]; exact h
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | p.1 = R} from h)]
      simp
    · have hnot : polarCoord.symm p ∉ {ζ : ℝ × ℝ | ζ.1 ^ 2 + ζ.2 ^ 2 = R ^ 2} := by
        intro hc
        change (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = R ^ 2 at hc
        rw [hsq, hiff] at hc
        exact h hc
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem (show p ∉ {p : ℝ × ℝ | p.1 = R} from h)]
      simp
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hzero]
  have hsub : {p : ℝ × ℝ | p.1 = R} = ({R} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by ext p; simp
  have hvol : volume ({p : ℝ × ℝ | p.1 = R}) = 0 := by
    rw [hsub, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
      Measure.prod_prod, Real.volume_singleton, zero_mul]
  have hae : (fun p : ℝ × ℝ => ({p : ℝ × ℝ | p.1 = R}).indicator (fun p => ENNReal.ofReal p.1) p) =ᵐ[volume.restrict polarCoord.target] (fun _ => 0) := by
    have h1 : volume.restrict polarCoord.target ({p : ℝ × ℝ | p.1 = R}) = 0 :=
      le_antisymm ((Measure.restrict_apply_le _ _).trans hvol.le) bot_le
    filter_upwards [compl_mem_ae_iff.mpr h1] with p hp
    simp [Set.indicator_of_notMem hp]
  rw [lintegral_congr_ae hae, lintegral_zero]

private lemma cpow_half_of_im_neg {w : ℂ} (hw : w.im < 0) :
    w ^ (1 / 2 : ℂ) = -Complex.I * (-w) ^ (1 / 2 : ℂ) := by
  have hw0 : w ≠ 0 := by intro h; rw [h, Complex.zero_im] at hw; exact lt_irrefl 0 hw
  have hnw0 : -w ≠ 0 := neg_ne_zero.mpr hw0
  have hsq : (-Complex.I * (-w) ^ (1 / 2 : ℂ)) ^ 2 = w := by
    have h1 : ((-w) ^ (1 / 2 : ℂ)) ^ 2 = -w := by
      rw [sq, ← Complex.cpow_add _ _ hnw0]; norm_num
    calc (-Complex.I * (-w) ^ (1 / 2 : ℂ)) ^ 2
        = Complex.I ^ 2 * ((-w) ^ (1 / 2 : ℂ)) ^ 2 := by ring
      _ = (-1) * (-w) := by rw [Complex.I_sq, h1]
      _ = w := by ring
  have hsq0 : (w ^ (1 / 2 : ℂ)) ^ 2 = w := by
    rw [sq, ← Complex.cpow_add _ _ hw0]; norm_num
  have hmul0 : (w ^ (1 / 2 : ℂ) - (-Complex.I * (-w) ^ (1 / 2 : ℂ))) *
      (w ^ (1 / 2 : ℂ) + (-Complex.I * (-w) ^ (1 / 2 : ℂ))) = 0 := by
    linear_combination hsq0 - hsq
  rcases mul_eq_zero.mp hmul0 with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have hre1 : 0 < (w ^ (1 / 2 : ℂ)).re := by
      rw [Complex.cpow_def_of_ne_zero hw0, Complex.exp_re]
      apply mul_pos (Real.exp_pos _)
      have him : (Complex.log w * (1 / 2 : ℂ)).im = w.arg / 2 := by simp [Complex.log_im]; ring
      rw [him]
      have harg_neg : w.arg < 0 := Complex.arg_neg_iff.mpr hw
      have harg_gt : -Real.pi < w.arg := Complex.neg_pi_lt_arg w
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    have hre2 : 0 < (-Complex.I * (-w) ^ (1 / 2 : ℂ)).re := by
      have hrew : (-Complex.I * (-w) ^ (1 / 2 : ℂ)).re = ((-w) ^ (1 / 2 : ℂ)).im := by simp
      rw [hrew, Complex.cpow_def_of_ne_zero hnw0, Complex.exp_im]
      apply mul_pos (Real.exp_pos _)
      have him : (Complex.log (-w) * (1 / 2 : ℂ)).im = (-w).arg / 2 := by simp [Complex.log_im]; ring
      rw [him]
      have hnw_im : 0 < (-w).im := by simp [hw]
      have harg_pos : 0 < (-w).arg :=
        lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hnw_im.le)
          (fun h => hnw_im.ne' (Complex.arg_eq_zero_iff.mp h.symm).2)
      have harg_lt : (-w).arg < Real.pi := by
        have hle := Complex.arg_le_pi (-w)
        have hne : (-w).arg ≠ Real.pi := by
          intro hpi
          have := (Complex.arg_eq_pi_iff.mp hpi).2
          linarith
        exact lt_of_le_of_ne hle hne
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hsum_re := congrArg Complex.re h
    simp only [Complex.add_re, Complex.zero_re] at hsum_re
    linarith

private lemma sommerfeld_causal (k : ℂ) (hk : IsCausalWavenumber k) (r : Space) (hr : 0 < r 2) :
    greenFn k r =
      ∫ ζ : ℝ × ℝ, ghat k ζ.1 ζ.2 (r 2) * planeWave ζ.1 ζ.2 (r 0) (r 1) := by
  by_cases hkim : 0 < k.im
  · exact sommerfeld_upperHalfPlane k hkim r hr
  · have hkim0 : k.im = 0 := le_antisymm (not_lt.mp hkim) hk.2
    set k0 : ℝ := k.re
    have hk0 : 0 < k0 := hk.1
    have hk_eq : k = (k0 : ℂ) := by apply Complex.ext <;> simp [k0, hkim0]
    set z : ℝ := r 2
    have hz : 0 < z := hr
    let kn : ℕ → ℂ := fun n => (k0 : ℂ) + Complex.I * ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)
    have hkn_im : ∀ n : ℕ, 0 < (kn n).im := fun n => by
      simp only [kn, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add]
      positivity
    have hkn_tendsto : Tendsto kn atTop (𝓝 k) := by
      have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 : Tendsto (fun n : ℕ => (k0 : ℂ) + Complex.I * (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ))
          atTop (𝓝 ((k0 : ℂ) + Complex.I * ((0 : ℝ) : ℂ))) :=
        tendsto_const_nhds.add ((Complex.continuous_ofReal.continuousAt.tendsto.comp h1).const_mul Complex.I)
      simpa [kn, hk_eq] using h2
    have hLHS_lim : Tendsto (fun n : ℕ => greenFn (kn n) r) atTop (𝓝 (greenFn k r)) := by
      have hc : Continuous (fun w : ℂ => greenFn w r) := by unfold greenFn; fun_prop
      exact hc.continuousAt.tendsto.comp hkn_tendsto
    have hRHS_lim : Tendsto (fun n : ℕ => ∫ ζ : ℝ × ℝ, ghat (kn n) ζ.1 ζ.2 z * planeWave ζ.1 ζ.2 (r 0) (r 1))
        atTop (𝓝 (∫ ζ : ℝ × ℝ, ghat k ζ.1 ζ.2 z * planeWave ζ.1 ζ.2 (r 0) (r 1))) := by
      have hae_off : ∀ᵐ ζ : ℝ × ℝ ∂volume, ζ.1 ^ 2 + ζ.2 ^ 2 ≠ k0 ^ 2 := by
        rw [ae_iff]
        have heq : {ζ : ℝ × ℝ | ¬(ζ.1 ^ 2 + ζ.2 ^ 2 ≠ k0 ^ 2)} = {ζ : ℝ × ℝ | ζ.1 ^ 2 + ζ.2 ^ 2 = k0 ^ 2} := by
          ext ζ; simp
        rw [heq]; exact measure_circle_zero k0 hk0
      have hbound_int : Integrable (fun ζ : ℝ × ℝ => ‖ghat k ζ.1 ζ.2 z‖) volume := by
        simpa using integrable_ghat_poly k hk z hz 0
      apply MeasureTheory.tendsto_integral_of_dominated_convergence (fun ζ : ℝ × ℝ => ‖ghat k ζ.1 ζ.2 z‖)
      · intro n
        have hpw : Measurable (fun ζ : ℝ × ℝ => planeWave ζ.1 ζ.2 (r 0) (r 1)) := by unfold planeWave; fun_prop
        exact ((measurable_ghat (kn n) z).mul hpw).aestronglyMeasurable
      · exact hbound_int
      · intro n
        filter_upwards [hae_off] with ζ hζ
        set δ : ℝ := 1 / ((n : ℝ) + 1)
        have hδ : 0 < δ := by positivity
        have hkn_re : (kn n).re = k0 := by
          simp only [kn, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
            Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_self, add_zero]
        have hkn_im' : (kn n).im = δ := by
          simp only [kn, δ, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
            Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add]
        simp only [norm_mul, norm_planeWave, mul_one, ghat, abs_of_pos hz, norm_div,
          Complex.norm_ofNat, norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
        have hβ_norm_ge : ‖sommerfeldRoot k ζ.1 ζ.2‖ ≤ ‖sommerfeldRoot (kn n) ζ.1 ζ.2‖ := by
          have hsq : ‖sommerfeldRoot k ζ.1 ζ.2‖ ^ 4 ≤ ‖sommerfeldRoot (kn n) ζ.1 ζ.2‖ ^ 4 := by
            have h1 : ‖sommerfeldRoot k ζ.1 ζ.2‖ ^ 4 = (ζ.1 ^ 2 + ζ.2 ^ 2 - k0 ^ 2) ^ 2 := by
              calc ‖sommerfeldRoot k ζ.1 ζ.2‖ ^ 4 = (‖sommerfeldRoot k ζ.1 ζ.2‖ ^ 2) ^ 2 := by ring
                _ = ‖(ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - k ^ 2‖ ^ 2 := by rw [norm_sommerfeldRoot_sq_eq]
                _ = (ζ.1 ^ 2 + ζ.2 ^ 2 - k0 ^ 2) ^ 2 := by
                    rw [hk_eq, show (ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - (k0 : ℂ) ^ 2 =
                      ((ζ.1 ^ 2 + ζ.2 ^ 2 - k0 ^ 2 : ℝ) : ℂ) by push_cast; ring,
                      Complex.norm_real, Real.norm_eq_abs, sq_abs]
            have h2 : ‖sommerfeldRoot (kn n) ζ.1 ζ.2‖ ^ 4 =
                (ζ.1 ^ 2 + ζ.2 ^ 2 - k0 ^ 2 + δ ^ 2) ^ 2 + (2 * k0 * δ) ^ 2 := by
              calc ‖sommerfeldRoot (kn n) ζ.1 ζ.2‖ ^ 4 = (‖sommerfeldRoot (kn n) ζ.1 ζ.2‖ ^ 2) ^ 2 := by ring
                _ = ‖(ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - (kn n) ^ 2‖ ^ 2 := by rw [norm_sommerfeldRoot_sq_eq]
                _ = Complex.normSq ((ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - (kn n) ^ 2) := Complex.sq_norm _
                _ = (ζ.1 ^ 2 + ζ.2 ^ 2 - k0 ^ 2 + δ ^ 2) ^ 2 + (2 * k0 * δ) ^ 2 := by
                    rw [Complex.normSq_apply]
                    have hre : ((ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - (kn n) ^ 2).re = ζ.1 ^ 2 + ζ.2 ^ 2 - k0 ^ 2 + δ ^ 2 := by
                      simp only [sq, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
                        Complex.ofReal_im, hkn_re, hkn_im']; ring
                    have him : ((ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - (kn n) ^ 2).im = -(2 * k0 * δ) := by
                      simp only [sq, Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
                        Complex.ofReal_im, hkn_re, hkn_im']; ring
                    rw [hre, him]; ring
            rw [h1, h2]
            nlinarith [sq_nonneg ζ.1, sq_nonneg ζ.2, sq_nonneg k0, sq_nonneg δ]
          have h2 : ‖sommerfeldRoot k ζ.1 ζ.2‖ ^ 2 ≤ ‖sommerfeldRoot (kn n) ζ.1 ζ.2‖ ^ 2 := by
            have : (‖sommerfeldRoot k ζ.1 ζ.2‖ ^ 2) ^ 2 ≤ (‖sommerfeldRoot (kn n) ζ.1 ζ.2‖ ^ 2) ^ 2 := by
              linarith
            exact le_of_sq_le_sq this (by positivity)
          exact le_of_sq_le_sq h2 (norm_nonneg _)
        have hβ_re_ge : (sommerfeldRoot k ζ.1 ζ.2).re ≤ (sommerfeldRoot (kn n) ζ.1 ζ.2).re := by
          by_cases hlt : ζ.1 ^ 2 + ζ.2 ^ 2 < k0 ^ 2
          · have hre0 : (sommerfeldRoot k ζ.1 ζ.2).re = 0 := by
              unfold sommerfeldRoot
              have hz' : (ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - k ^ 2 = ((ζ.1 ^ 2 + ζ.2 ^ 2 - k0 ^ 2 : ℝ) : ℂ) := by
                rw [hk_eq]; push_cast; ring
              rw [hz', if_pos ⟨by simp only [Complex.ofReal_im], by simp only [Complex.ofReal_re]; linarith⟩]; simp
            rw [hre0]; exact sommerfeldRoot_re_nonneg (kn n) ζ.1 ζ.2
          · push Not at hlt
            have hre_k : (sommerfeldRoot k ζ.1 ζ.2).re = Real.sqrt (ζ.1 ^ 2 + ζ.2 ^ 2 - k0 ^ 2) := by
              unfold sommerfeldRoot
              have hz' : (ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - k ^ 2 = ((ζ.1 ^ 2 + ζ.2 ^ 2 - k0 ^ 2 : ℝ) : ℂ) := by
                rw [hk_eq]; push_cast; ring
              rw [hz', if_neg (by simp only [Complex.ofReal_im, Complex.ofReal_re, true_and, not_lt]; linarith),
                show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
                ← Complex.ofReal_cpow (by linarith)]
              simp [Real.sqrt_eq_rpow]
            rw [hre_k]
            have hsq : Real.sqrt (ζ.1 ^ 2 + ζ.2 ^ 2 - k0 ^ 2) ^ 2 ≤ (sommerfeldRoot (kn n) ζ.1 ζ.2).re ^ 2 := by
              rw [Real.sq_sqrt (by linarith)]
              have h1 := sommerfeldRoot_re_sq_ge (kn n) ζ.1 ζ.2
              have hre_kn : ((ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - (kn n) ^ 2).re =
                  ζ.1 ^ 2 + ζ.2 ^ 2 - k0 ^ 2 + δ ^ 2 := by
                simp only [sq, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
                  Complex.ofReal_im, hkn_re, hkn_im']; ring
              rw [hre_kn] at h1
              nlinarith [sq_nonneg δ]
            exact le_of_sq_le_sq hsq (sommerfeldRoot_re_nonneg (kn n) ζ.1 ζ.2)
        have hβk_pos : 0 < ‖sommerfeldRoot k ζ.1 ζ.2‖ := by
          have h1 : 0 < ‖sommerfeldRoot k ζ.1 ζ.2‖ ^ 2 := by
            rw [norm_sommerfeldRoot_sq_eq, hk_eq,
              show (ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - (k0 : ℂ) ^ 2 = ((ζ.1 ^ 2 + ζ.2 ^ 2 - k0 ^ 2 : ℝ) : ℂ) by push_cast; ring,
              Complex.norm_real, Real.norm_eq_abs]
            exact abs_pos.mpr (sub_ne_zero.mpr hζ)
          nlinarith [norm_nonneg (sommerfeldRoot k ζ.1 ζ.2)]
        have hexp_le : ‖Complex.exp (-(sommerfeldRoot (kn n) ζ.1 ζ.2) * (z : ℂ))‖ ≤
            ‖Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ))‖ := by
          rw [Complex.norm_exp, Complex.norm_exp]
          have h1 : (-(sommerfeldRoot (kn n) ζ.1 ζ.2) * (z : ℂ)).re = -(sommerfeldRoot (kn n) ζ.1 ζ.2).re * z := by simp
          have h2 : (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ)).re = -(sommerfeldRoot k ζ.1 ζ.2).re * z := by simp
          rw [h1, h2]; exact Real.exp_le_exp.mpr (by nlinarith)
        exact div_le_div₀ (norm_nonneg _) hexp_le (by positivity) (by gcongr)
      · filter_upwards [hae_off] with ζ hζ
        have hβ_lim : Tendsto (fun n : ℕ => sommerfeldRoot (kn n) ζ.1 ζ.2) atTop (𝓝 (sommerfeldRoot k ζ.1 ζ.2)) := by
          have hw_lim : Tendsto (fun n : ℕ => (ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - (kn n) ^ 2)
              atTop (𝓝 ((ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - k ^ 2)) :=
            tendsto_const_nhds.sub (hkn_tendsto.pow 2)
          have hβ_eq_n : ∀ n : ℕ, sommerfeldRoot (kn n) ζ.1 ζ.2 =
              ((ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - (kn n) ^ 2) ^ (1 / 2 : ℂ) :=
            fun n => sommerfeldRoot_eq_cpow_of_im_pos (hkn_im n) ζ.1 ζ.2
          simp_rw [hβ_eq_n]
          rcases lt_or_gt_of_ne hζ with hlt | hgt
          · have hcpow_eq : ∀ n : ℕ, ((ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - (kn n) ^ 2) ^ (1 / 2 : ℂ) =
                -Complex.I * (-((ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - (kn n) ^ 2)) ^ (1 / 2 : ℂ) := by
              intro n
              apply cpow_half_of_im_neg
              have hkn_re : (kn n).re = k0 := by
                simp only [kn, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
                  Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_self, add_zero]
              have hkn_im' : (kn n).im = 1 / ((n : ℝ) + 1) := by
                simp only [kn, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
                  Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add]
              have him : ((ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - (kn n) ^ 2).im =
                  -(2 * k0 * (1 / ((n : ℝ) + 1))) := by
                simp only [sq, Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
                  Complex.ofReal_im, hkn_re, hkn_im']; ring
              rw [him]; exact neg_lt_zero.mpr (by positivity)
            simp_rw [hcpow_eq]
            have hnw_lim : Tendsto (fun n : ℕ => -((ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - (kn n) ^ 2))
                atTop (𝓝 (((k0 ^ 2 - (ζ.1 ^ 2 + ζ.2 ^ 2) : ℝ) : ℂ))) := by
              have h := hw_lim.neg
              convert h using 2
              rw [hk_eq]; push_cast; ring
            have hpos : 0 < k0 ^ 2 - (ζ.1 ^ 2 + ζ.2 ^ 2) := by linarith
            have hslit : (((k0 ^ 2 - (ζ.1 ^ 2 + ζ.2 ^ 2) : ℝ) : ℂ)) ∈ Complex.slitPlane :=
              Or.inl (by simp only [Complex.ofReal_re]; exact hpos)
            have hlog_c : ContinuousAt (fun w : ℂ => w ^ (1 / 2 : ℂ)) (((k0 ^ 2 - (ζ.1 ^ 2 + ζ.2 ^ 2) : ℝ) : ℂ)) := by
              have h1 : ContinuousAt (fun w : ℂ => Complex.exp (Complex.log w * (1 / 2 : ℂ)))
                  (((k0 ^ 2 - (ζ.1 ^ 2 + ζ.2 ^ 2) : ℝ) : ℂ)) :=
                Complex.continuous_exp.continuousAt.comp
                  (((Complex.hasDerivAt_log hslit).continuousAt).mul (continuousAt_const (y := (1 / 2 : ℂ))))
              have hne : (((k0 ^ 2 - (ζ.1 ^ 2 + ζ.2 ^ 2) : ℝ) : ℂ)) ≠ 0 := Complex.slitPlane_ne_zero hslit
              exact h1.congr ((continuousAt_id.eventually_ne hne).mono fun w hw => (Complex.cpow_def_of_ne_zero hw _).symm)
            have hlim := (hlog_c.tendsto.comp hnw_lim).const_mul (-Complex.I)
            have hlim_eq : -Complex.I * (((k0 ^ 2 - (ζ.1 ^ 2 + ζ.2 ^ 2) : ℝ) : ℂ)) ^ (1 / 2 : ℂ) =
                sommerfeldRoot k ζ.1 ζ.2 := by
              unfold sommerfeldRoot
              have hz' : (ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - k ^ 2 = ((ζ.1 ^ 2 + ζ.2 ^ 2 - k0 ^ 2 : ℝ) : ℂ) := by
                rw [hk_eq]; push_cast; ring
              rw [hz', if_pos ⟨by simp only [Complex.ofReal_im], by simp only [Complex.ofReal_re]; linarith⟩]
              simp only [Complex.ofReal_re]
              rw [show -(ζ.1 ^ 2 + ζ.2 ^ 2 - k0 ^ 2) = k0 ^ 2 - (ζ.1 ^ 2 + ζ.2 ^ 2) by ring,
                show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hpos.le]
              norm_cast; rw [Real.sqrt_eq_rpow]
            rw [hlim_eq] at hlim
            exact hlim
          · have hpos : 0 < ζ.1 ^ 2 + ζ.2 ^ 2 - k0 ^ 2 := by linarith
            have hz' : (ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - k ^ 2 = ((ζ.1 ^ 2 + ζ.2 ^ 2 - k0 ^ 2 : ℝ) : ℂ) := by
              rw [hk_eq]; push_cast; ring
            have hslit : ((ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - k ^ 2) ∈ Complex.slitPlane := by
              rw [hz']; exact Or.inl (by simp only [Complex.ofReal_re]; exact hpos)
            have hlog_c : ContinuousAt (fun w : ℂ => w ^ (1 / 2 : ℂ)) ((ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - k ^ 2) := by
              have h1 : ContinuousAt (fun w : ℂ => Complex.exp (Complex.log w * (1 / 2 : ℂ)))
                  ((ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - k ^ 2) :=
                Complex.continuous_exp.continuousAt.comp
                  (((Complex.hasDerivAt_log hslit).continuousAt).mul (continuousAt_const (y := (1 / 2 : ℂ))))
              have hne := Complex.slitPlane_ne_zero hslit
              exact h1.congr ((continuousAt_id.eventually_ne hne).mono fun w hw => (Complex.cpow_def_of_ne_zero hw _).symm)
            have hlim := hlog_c.tendsto.comp hw_lim
            have hlim_eq : ((ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - k ^ 2) ^ (1 / 2 : ℂ) = sommerfeldRoot k ζ.1 ζ.2 := by
              unfold sommerfeldRoot
              rw [hz', if_neg (by simp only [Complex.ofReal_im, Complex.ofReal_re, true_and, not_lt]; linarith)]
            rw [hlim_eq] at hlim
            exact hlim
        have hβk_ne : sommerfeldRoot k ζ.1 ζ.2 ≠ 0 := by
          intro h0
          have h1 := sommerfeldRoot_sq k ζ.1 ζ.2
          rw [h0, zero_pow two_ne_zero, hk_eq] at h1
          have h2 : ((ζ.1 ^ 2 + ζ.2 ^ 2 - k0 ^ 2 : ℝ) : ℂ) = 0 := by
            push_cast; linear_combination -h1
          exact hζ (sub_eq_zero.mp (Complex.ofReal_eq_zero.mp h2))
        have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        have hden_ne : 8 * (Real.pi : ℂ) ^ 2 * sommerfeldRoot k ζ.1 ζ.2 ≠ 0 :=
          mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hpi)) hβk_ne
        have hghat_lim : Tendsto (fun n : ℕ => ghat (kn n) ζ.1 ζ.2 z) atTop (𝓝 (ghat k ζ.1 ζ.2 z)) := by
          unfold ghat
          exact ((Complex.continuous_exp.continuousAt.tendsto.comp
            (hβ_lim.neg.mul_const (((|z| : ℝ) : ℂ))))).div (hβ_lim.const_mul (8 * (Real.pi : ℂ) ^ 2)) hden_ne
        exact hghat_lim.mul_const _
    have heq_n : ∀ n : ℕ, greenFn (kn n) r =
        ∫ ζ : ℝ × ℝ, ghat (kn n) ζ.1 ζ.2 z * planeWave ζ.1 ζ.2 (r 0) (r 1) :=
      fun n => sommerfeld_upperHalfPlane (kn n) (hkn_im n) r hr
    exact tendsto_nhds_unique hLHS_lim (hRHS_lim.congr (fun n => (heq_n n).symm))

/-! ### Part 7: Volume potential equals spectral integral + differentiation -/

private lemma exists_z_upper_bound {f : Space → ℂ} (hfc : HasCompactSupport f)
    (hfV : tsupport f ⊆ {q : Space | q 2 < 0}) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ tsupport f, q 2 ≤ -δ := by
  by_cases hemp : (tsupport f).Nonempty
  · have hcont : ContinuousOn (fun q : Space => q 2) (tsupport f) :=
      (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.continuousOn
    obtain ⟨q₀, hq₀_mem, hq₀_max⟩ := hfc.isCompact.exists_isMaxOn hemp hcont
    have hneg : q₀ 2 < 0 := hfV hq₀_mem
    refine ⟨-(q₀ 2), neg_pos.mpr hneg, fun q hq => ?_⟩
    have hle : q 2 ≤ q₀ 2 := hq₀_max hq
    linarith
  · rw [Set.not_nonempty_iff_eq_empty] at hemp
    exact ⟨1, zero_lt_one, fun q hq => by rw [hemp] at hq; exact hq.elim⟩

private lemma volumePotential_eq_spectral (k : ℂ) (hk : IsCausalWavenumber k)
    (f : Space → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfV : tsupport f ⊆ {q : Space | q 2 < 0}) (p : Space) (hp : 0 < p 2) :
    volumePotential k f p =
      ∫ ζ : ℝ × ℝ, ghat k ζ.1 ζ.2 (p 2) *
        (∫ q : Space, Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) * f q *
          Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1)))) *
        planeWave ζ.1 ζ.2 (p 0) (p 1) := by
  obtain ⟨δ, hδ, hδ_le⟩ := exists_z_upper_bound hfc hfV
  have hvp_eq : volumePotential k f p =
      ∫ q : Space, ∫ ζ : ℝ × ℝ,
        ghat k ζ.1 ζ.2 (p 2) * (Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) * f q *
          Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1)))) *
        planeWave ζ.1 ζ.2 (p 0) (p 1) := by
    unfold volumePotential
    congr 1; ext q
    by_cases hfq : f q = 0
    · simp [hfq]
    · have hq_mem : q ∈ tsupport f := subset_tsupport f hfq
      have hq_neg : q 2 < 0 := hfV hq_mem
      have hdiff_pos : 0 < (p - q) 2 := by change 0 < p 2 - q 2; linarith
      rw [sommerfeld_causal k hk (p - q) hdiff_pos, ← integral_mul_const]
      congr 1; ext ζ
      have hsub2 : (p - q) 2 = p 2 - q 2 := rfl
      have hsub0 : (p - q) 0 = p 0 - q 0 := rfl
      have hsub1 : (p - q) 1 = p 1 - q 1 := rfl
      have hghat_split : ghat k ζ.1 ζ.2 (p 2 - q 2) =
          ghat k ζ.1 ζ.2 (p 2) * Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) := by
        simp only [ghat, abs_of_pos (by linarith : 0 < p 2 - q 2), abs_of_pos hp]
        rw [div_mul_eq_mul_div, ← Complex.exp_add]
        congr 2; push_cast; ring
      have hpw_split : planeWave ζ.1 ζ.2 (p 0 - q 0) (p 1 - q 1) =
          Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1))) * planeWave ζ.1 ζ.2 (p 0) (p 1) := by
        simp only [planeWave, ← Complex.exp_add]
        congr 1; push_cast; ring
      rw [hsub2, hsub0, hsub1, hghat_split, hpw_split]; ring
  rw [hvp_eq]
  let K : Space → ℝ × ℝ → ℂ := fun q ζ =>
    ghat k ζ.1 ζ.2 (p 2) * (Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) * f q *
      Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1)))) *
    planeWave ζ.1 ζ.2 (p 0) (p 1)
  have hK_int : Integrable (Function.uncurry K) (volume.prod volume) := by
    have hK_meas : AEStronglyMeasurable (Function.uncurry K) (volume.prod volume) := by
      have hβ : Measurable (fun x : Space × (ℝ × ℝ) => sommerfeldRoot k x.2.1 x.2.2) :=
        (measurable_sommerfeldRoot k).comp measurable_snd
      have hg : Measurable (fun x : Space × (ℝ × ℝ) => ghat k x.2.1 x.2.2 (p 2)) :=
        (measurable_ghat k (p 2)).comp measurable_snd
      have hf' : Measurable (fun x : Space × (ℝ × ℝ) => f x.1) :=
        hf.measurable.comp measurable_fst
      have hq0 : Measurable (fun x : Space × (ℝ × ℝ) => ((x.1 0 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.measurable.comp ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).continuous.measurable.comp measurable_fst)
      have hq1 : Measurable (fun x : Space × (ℝ × ℝ) => ((x.1 1 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.measurable.comp ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).continuous.measurable.comp measurable_fst)
      have hq2 : Measurable (fun x : Space × (ℝ × ℝ) => ((x.1 2 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.measurable.comp ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.measurable.comp measurable_fst)
      have hexp1 : Measurable (fun x : Space × (ℝ × ℝ) => Complex.exp (sommerfeldRoot k x.2.1 x.2.2 * x.1 2)) :=
        Complex.continuous_exp.measurable.comp (hβ.mul hq2)
      have hexp2 : Measurable (fun x : Space × (ℝ × ℝ) =>
          Complex.exp (-(Complex.I * ((x.2.1 : ℂ) * (x.1 0 : ℂ) + (x.2.2 : ℂ) * (x.1 1 : ℂ))))) :=
        Complex.continuous_exp.measurable.comp
          ((measurable_const.mul
            (((Complex.continuous_ofReal.measurable.comp (measurable_fst.comp measurable_snd)).mul hq0).add
             ((Complex.continuous_ofReal.measurable.comp (measurable_snd.comp measurable_snd)).mul hq1))).neg)
      have hpw : Measurable (fun x : Space × (ℝ × ℝ) => planeWave x.2.1 x.2.2 (p 0) (p 1)) := by
        unfold planeWave; fun_prop
      exact ((hg.mul ((hexp1.mul hf').mul hexp2)).mul hpw).aestronglyMeasurable
    have hbound : Integrable (fun x : Space × (ℝ × ℝ) => ‖f x.1‖ * ‖ghat k x.2.1 x.2.2 (p 2)‖) (volume.prod volume) :=
      (hf.integrable_of_hasCompactSupport hfc).norm.mul_prod
        (by simpa using integrable_ghat_poly k hk (p 2) hp 0)
    refine Integrable.mono' hbound hK_meas (Eventually.of_forall fun ⟨q, ζ⟩ => ?_)
    by_cases hfq : f q = 0
    · simp [K, hfq]
    · have hq_neg : q 2 < 0 := hfV (subset_tsupport f hfq)
      have hexp1_le : ‖Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * (q 2 : ℂ))‖ ≤ 1 := by
        rw [Complex.norm_exp]
        apply Real.exp_le_one_iff.mpr
        have hre : (sommerfeldRoot k ζ.1 ζ.2 * (q 2 : ℂ)).re = (sommerfeldRoot k ζ.1 ζ.2).re * q 2 := by simp
        rw [hre]; nlinarith [sommerfeldRoot_re_nonneg k ζ.1 ζ.2]
      have hexp2_eq : ‖Complex.exp (-(Complex.I * ((ζ.1 : ℂ) * (q 0 : ℂ) + (ζ.2 : ℂ) * (q 1 : ℂ))))‖ = 1 := by
        have : -(Complex.I * ((ζ.1 : ℂ) * (q 0 : ℂ) + (ζ.2 : ℂ) * (q 1 : ℂ))) =
            ((-(ζ.1 * q 0 + ζ.2 * q 1) : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I]
      simp only [Function.uncurry, K, norm_mul, norm_planeWave, hexp2_eq, mul_one]
      calc ‖ghat k ζ.1 ζ.2 (p 2)‖ * (‖Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * (q 2 : ℂ))‖ * ‖f q‖)
          ≤ ‖ghat k ζ.1 ζ.2 (p 2)‖ * (1 * ‖f q‖) := by gcongr
        _ = ‖f q‖ * ‖ghat k ζ.1 ζ.2 (p 2)‖ := by ring
  rw [MeasureTheory.integral_integral_swap hK_int]
  congr 1; ext ζ
  rw [← integral_const_mul, ← integral_mul_const]

private lemma hasFDerivAt_expMode (α : ℂ) (ξ η : ℝ) (p : Space) :
    HasFDerivAt (fun q : Space => Complex.exp (α * (q 2 : ℂ)) * mode ξ η q)
      ((Complex.exp (α * (p 2 : ℂ)) * mode ξ η p) •
        (α • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3))) +
          Complex.I • ((ξ : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3))) +
            (η : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)))))) p := by
  have h0 : HasFDerivAt (fun q : Space => ((q 0 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3))) p :=
    Complex.ofRealCLM.hasFDerivAt.comp p (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).hasFDerivAt
  have h1 : HasFDerivAt (fun q : Space => ((q 1 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3))) p :=
    Complex.ofRealCLM.hasFDerivAt.comp p (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).hasFDerivAt
  have h2 : HasFDerivAt (fun q : Space => ((q 2 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3))) p :=
    Complex.ofRealCLM.hasFDerivAt.comp p (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).hasFDerivAt
  have harg := (h2.const_mul α).add (((h0.const_mul (ξ : ℂ)).add (h1.const_mul (η : ℂ))).const_mul Complex.I)
  have hexp := ((Complex.hasDerivAt_exp _).hasFDerivAt.restrictScalars ℝ).comp p harg
  have hexp' : HasFDerivAt (fun q : Space => Complex.exp (α * (q 2 : ℂ)) * mode ξ η q) _ p :=
    hexp.congr_of_eventuallyEq (Eventually.of_forall fun q => by
      simp [Function.comp, Complex.exp_add, mode, planeWave])
  refine hexp'.congr_fderiv ?_
  ext v
  simp [Complex.exp_add, mode, planeWave, smul_eq_mul, mul_comm]

private lemma pd_volumePotential_spectral (k : ℂ) (hk : IsCausalWavenumber k)
    (f : Space → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfV : tsupport f ⊆ {q : Space | q 2 < 0}) (p : Space) (hp : 0 < p 2) (i : Fin 3) :
    pd i (volumePotential k f) p =
      ∫ ζ : ℝ × ℝ,
        (match i with | 0 => Complex.I * ζ.1 | 1 => Complex.I * ζ.2 | 2 => -(sommerfeldRoot k ζ.1 ζ.2)) *
        ghat k ζ.1 ζ.2 (p 2) *
        (∫ q : Space, Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) * f q *
          Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1)))) *
        planeWave ζ.1 ζ.2 (p 0) (p 1) := by
  obtain ⟨δ, hδ, hδ_le⟩ := exists_z_upper_bound hfc hfV
  set w : ℝ × ℝ → ℂ := fun ζ =>
    ghat k ζ.1 ζ.2 0 * (∫ q : Space, Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) * f q *
      Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1))))
  let F : Space → ℝ × ℝ → ℂ := fun p' ζ =>
    w ζ * (Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (p' 2 : ℂ)) * mode ζ.1 ζ.2 p')
  let F' : Space → ℝ × ℝ → Space →L[ℝ] ℂ := fun p' ζ =>
    (w ζ * (Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (p' 2 : ℂ)) * mode ζ.1 ζ.2 p')) •
      (-(sommerfeldRoot k ζ.1 ζ.2) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3))) +
        Complex.I • ((ζ.1 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3))) +
          (ζ.2 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)))))
  have isOpen_uhs : IsOpen upperHalfSpace :=
    isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous
  have hev_vp : volumePotential k f =ᶠ[𝓝 p] fun p' => ∫ ζ : ℝ × ℝ, F p' ζ := by
    filter_upwards [isOpen_uhs.mem_nhds hp] with p' hp'
    have hp'_pos : 0 < p' 2 := hp'
    rw [volumePotential_eq_spectral k hk f hf hfc hfV p' hp'_pos]
    congr 1; ext ζ
    simp only [F, w, ghat, mode, abs_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, abs_of_pos hp'_pos]
    ring
  rw [pd, hev_vp.fderiv_eq]
  change pd i (fun p' => ∫ ζ : ℝ × ℝ, F p' ζ) p = _
  set Cf : ℝ := ∫ q : Space, ‖f q‖
  have hCf_nn : 0 ≤ Cf := integral_nonneg fun _ => norm_nonneg _
  have hw_bound : ∀ ζ : ℝ × ℝ, ‖w ζ‖ ≤ Cf * ‖ghat k ζ.1 ζ.2 δ‖ := by
    intro ζ
    have h1 : ‖∫ q : Space, Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) * f q *
        Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1)))‖ ≤
        Real.exp (-(sommerfeldRoot k ζ.1 ζ.2).re * δ) * Cf := by
      have hint_f : Integrable (fun q : Space => Real.exp (-(sommerfeldRoot k ζ.1 ζ.2).re * δ) * ‖f q‖) :=
        (hf.integrable_of_hasCompactSupport hfc).norm.const_mul _
      calc ‖∫ q : Space, Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) * f q *
              Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1)))‖
          ≤ ∫ q : Space, ‖Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) * f q *
              Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1)))‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ q : Space, Real.exp (-(sommerfeldRoot k ζ.1 ζ.2).re * δ) * ‖f q‖ := by
            apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint_f
            refine Eventually.of_forall fun q => ?_
            by_cases hfq : f q = 0
            · simp [hfq]
            · have hq_le : q 2 ≤ -δ := hδ_le q (subset_tsupport f hfq)
              have hexp2 : ‖Complex.exp (-(Complex.I * ((ζ.1 : ℂ) * (q 0 : ℂ) + (ζ.2 : ℂ) * (q 1 : ℂ))))‖ = 1 := by
                have : -(Complex.I * ((ζ.1 : ℂ) * (q 0 : ℂ) + (ζ.2 : ℂ) * (q 1 : ℂ))) =
                    ((-(ζ.1 * q 0 + ζ.2 * q 1) : ℝ) : ℂ) * Complex.I := by push_cast; ring
                rw [this, Complex.norm_exp_ofReal_mul_I]
              dsimp only
              rw [norm_mul, norm_mul, hexp2, mul_one, Complex.norm_exp]
              have hre : (sommerfeldRoot k ζ.1 ζ.2 * (q 2 : ℂ)).re = (sommerfeldRoot k ζ.1 ζ.2).re * q 2 := by simp
              rw [hre]
              have hexp1 : Real.exp ((sommerfeldRoot k ζ.1 ζ.2).re * q 2) ≤ Real.exp (-(sommerfeldRoot k ζ.1 ζ.2).re * δ) :=
                Real.exp_le_exp.mpr (by nlinarith [sommerfeldRoot_re_nonneg k ζ.1 ζ.2])
              exact mul_le_mul_of_nonneg_right hexp1 (norm_nonneg _)
        _ = Real.exp (-(sommerfeldRoot k ζ.1 ζ.2).re * δ) * Cf := integral_const_mul _ _
    have hghat_norm : ‖ghat k ζ.1 ζ.2 0‖ * Real.exp (-(sommerfeldRoot k ζ.1 ζ.2).re * δ) = ‖ghat k ζ.1 ζ.2 δ‖ := by
      simp only [ghat, abs_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, abs_of_pos hδ,
        norm_div, norm_one, Complex.norm_exp]
      have hre : (-(sommerfeldRoot k ζ.1 ζ.2) * (δ : ℂ)).re = -(sommerfeldRoot k ζ.1 ζ.2).re * δ := by simp
      rw [hre]; ring
    simp only [w, norm_mul]
    calc ‖ghat k ζ.1 ζ.2 0‖ * ‖∫ q : Space, Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) * f q *
            Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1)))‖
        ≤ ‖ghat k ζ.1 ζ.2 0‖ * (Real.exp (-(sommerfeldRoot k ζ.1 ζ.2).re * δ) * Cf) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = Cf * (‖ghat k ζ.1 ζ.2 0‖ * Real.exp (-(sommerfeldRoot k ζ.1 ζ.2).re * δ)) := by ring
      _ = Cf * ‖ghat k ζ.1 ζ.2 δ‖ := by rw [hghat_norm]
  have hwm : AEStronglyMeasurable w volume := by
    have hinner : StronglyMeasurable (fun ζ : ℝ × ℝ =>
        ∫ q : Space, Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) * f q *
          Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1)))) := by
      apply StronglyMeasurable.integral_prod_right
      have hβ : Measurable (fun x : (ℝ × ℝ) × Space => sommerfeldRoot k x.1.1 x.1.2) :=
        (measurable_sommerfeldRoot k).comp measurable_fst
      have hf' : Measurable (fun x : (ℝ × ℝ) × Space => f x.2) := hf.measurable.comp measurable_snd
      have hq0 : Measurable (fun x : (ℝ × ℝ) × Space => ((x.2 0 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.measurable.comp ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).continuous.measurable.comp measurable_snd)
      have hq1 : Measurable (fun x : (ℝ × ℝ) × Space => ((x.2 1 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.measurable.comp ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).continuous.measurable.comp measurable_snd)
      have hq2 : Measurable (fun x : (ℝ × ℝ) × Space => ((x.2 2 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.measurable.comp ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.measurable.comp measurable_snd)
      have hexp1 : Measurable (fun x : (ℝ × ℝ) × Space => Complex.exp (sommerfeldRoot k x.1.1 x.1.2 * x.2 2)) :=
        Complex.continuous_exp.measurable.comp (hβ.mul hq2)
      have hexp2 : Measurable (fun x : (ℝ × ℝ) × Space =>
          Complex.exp (-(Complex.I * ((x.1.1 : ℂ) * (x.2 0 : ℂ) + (x.1.2 : ℂ) * (x.2 1 : ℂ))))) :=
        Complex.continuous_exp.measurable.comp
          ((measurable_const.mul
            (((Complex.continuous_ofReal.measurable.comp (measurable_fst.comp measurable_fst)).mul hq0).add
             ((Complex.continuous_ofReal.measurable.comp (measurable_snd.comp measurable_fst)).mul hq1))).neg)
      exact ((hexp1.mul hf').mul hexp2).stronglyMeasurable
    exact (measurable_ghat k 0).aestronglyMeasurable.mul hinner.aestronglyMeasurable
  let bound : ℝ × ℝ → ℝ := fun ζ => ((3 + ‖k‖) * Cf) * ((1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 δ‖)
  have hbound_int : Integrable bound volume := by
    simpa [bound] using (integrable_ghat_poly k hk δ hδ 1).const_mul ((3 + ‖k‖) * Cf)
  have hproj_norm : ∀ j : Fin 3, ‖Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) j)‖ ≤ 1 := by
    intro j; refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real, one_mul]
    exact PiLp.norm_apply_le v j
  have hF_meas : ∀ q : Space, AEStronglyMeasurable (F q) volume := by
    intro q
    have hβ := measurable_sommerfeldRoot k
    have hmode : Measurable (fun ζ : ℝ × ℝ => Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (q 2 : ℂ)) * mode ζ.1 ζ.2 q) := by
      unfold mode planeWave
      exact (Complex.continuous_exp.measurable.comp (hβ.neg.mul measurable_const)).mul
        (Complex.continuous_exp.measurable.comp (measurable_const.mul
          (((Complex.continuous_ofReal.measurable.comp measurable_fst).mul measurable_const).add
            ((Complex.continuous_ofReal.measurable.comp measurable_snd).mul measurable_const))))
    exact hwm.mul hmode.aestronglyMeasurable
  have hF_int : Integrable (F p) volume := by
    have h0 : Integrable (fun ζ : ℝ × ℝ => ‖ghat k ζ.1 ζ.2 δ‖) volume := by
      simpa using integrable_ghat_poly k hk δ hδ 0
    refine Integrable.mono' (h0.const_mul Cf) (hF_meas p) (Eventually.of_forall fun ζ => ?_)
    have hmode1 : ‖mode ζ.1 ζ.2 p‖ = 1 := norm_planeWave ζ.1 ζ.2 (p 0) (p 1)
    simp only [F, norm_mul, hmode1, mul_one]
    calc ‖w ζ‖ * ‖Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (p 2 : ℂ))‖
        ≤ (Cf * ‖ghat k ζ.1 ζ.2 δ‖) * 1 := mul_le_mul (hw_bound ζ) (norm_exp_neg_sommerfeldRoot_le_one k ζ.1 ζ.2 (p 2) hp.le) (norm_nonneg _) (by positivity)
      _ = Cf * ‖ghat k ζ.1 ζ.2 δ‖ := mul_one _
  have hF'_meas : AEStronglyMeasurable (F' p) volume := by
    have hβ := measurable_sommerfeldRoot k
    have hm2 : Measurable (fun ζ : ℝ × ℝ => (-(sommerfeldRoot k ζ.1 ζ.2) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3))) : Space →L[ℝ] ℂ)) :=
      hβ.neg.smul measurable_const
    have hm0 : Measurable (fun ζ : ℝ × ℝ => ((ζ.1 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3))) : Space →L[ℝ] ℂ)) :=
      (Complex.continuous_ofReal.measurable.comp measurable_fst).smul measurable_const
    have hm1 : Measurable (fun ζ : ℝ × ℝ => ((ζ.2 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3))) : Space →L[ℝ] ℂ)) :=
      (Complex.continuous_ofReal.measurable.comp measurable_snd).smul measurable_const
    exact (hF_meas p).smul (hm2.add ((hm0.add hm1).const_smul Complex.I)).aestronglyMeasurable
  have hF'_bound : ∀ ζ : ℝ × ℝ, ∀ q ∈ Metric.ball p (p 2 / 2), ‖F' q ζ‖ ≤ bound ζ := by
    intro ζ q hq
    have hq2 : 0 ≤ q 2 := by
      have hd : ‖q - p‖ < p 2 / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hq
      have hcoord : |q 2 - p 2| ≤ ‖q - p‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (q - p) (2 : Fin 3)
      linarith [(abs_le.mp (hcoord.trans hd.le)).1]
    have hmode1 : ‖mode ζ.1 ζ.2 q‖ = 1 := norm_planeWave ζ.1 ζ.2 (q 0) (q 1)
    simp only [F', norm_smul, norm_mul, hmode1, mul_one]
    have hL_le : ‖-(sommerfeldRoot k ζ.1 ζ.2) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3))) +
          Complex.I • ((ζ.1 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3))) +
            (ζ.2 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3))))‖ ≤
        (3 + ‖k‖) * (1 + ζ.1 ^ 2 + ζ.2 ^ 2) := by
      have hfac1 : ‖-(sommerfeldRoot k ζ.1 ζ.2) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3))) +
            Complex.I • ((ζ.1 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3))) +
              (ζ.2 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3))))‖ ≤
          |ζ.1| + |ζ.2| + ‖sommerfeldRoot k ζ.1 ζ.2‖ := by
        calc _ ≤ ‖-(sommerfeldRoot k ζ.1 ζ.2) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)))‖ +
              ‖Complex.I • ((ζ.1 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3))) +
                (ζ.2 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3))))‖ := norm_add_le _ _
          _ ≤ ‖sommerfeldRoot k ζ.1 ζ.2‖ * 1 + (|ζ.1| * 1 + |ζ.2| * 1) := by
              gcongr
              · rw [norm_smul, norm_neg]; exact mul_le_mul_of_nonneg_left (hproj_norm 2) (norm_nonneg _)
              · rw [norm_smul, Complex.norm_I, one_mul]
                calc _ ≤ ‖(ζ.1 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)))‖ +
                      ‖(ζ.2 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)))‖ := norm_add_le _ _
                  _ ≤ |ζ.1| * 1 + |ζ.2| * 1 := by
                      gcongr
                      · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hproj_norm 0) (abs_nonneg _)
                      · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hproj_norm 1) (abs_nonneg _)
          _ = |ζ.1| + |ζ.2| + ‖sommerfeldRoot k ζ.1 ζ.2‖ := by ring
      have hsqrt_le : Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2) ≤ 1 + ζ.1 ^ 2 + ζ.2 ^ 2 :=
        Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [sq_nonneg ζ.1, sq_nonneg ζ.2]⟩
      have hx : |ζ.1| ≤ 1 + ζ.1 ^ 2 + ζ.2 ^ 2 := by
        have h1 : |ζ.1| ≤ Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2) := by
          rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ζ.2])
        linarith
      have hy : |ζ.2| ≤ 1 + ζ.1 ^ 2 + ζ.2 ^ 2 := by
        have h1 : |ζ.2| ≤ Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2) := by
          rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ζ.1])
        linarith
      have hβle : ‖sommerfeldRoot k ζ.1 ζ.2‖ ≤ (1 + ‖k‖) * (1 + ζ.1 ^ 2 + ζ.2 ^ 2) :=
        (norm_sommerfeldRoot_le k ζ.1 ζ.2).trans (by gcongr)
      linarith
    have hexp_le := norm_exp_neg_sommerfeldRoot_le_one k ζ.1 ζ.2 (q 2) hq2
    calc ‖w ζ‖ * ‖Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (q 2 : ℂ))‖ * _
        ≤ (Cf * ‖ghat k ζ.1 ζ.2 δ‖) * 1 * ((3 + ‖k‖) * (1 + ζ.1 ^ 2 + ζ.2 ^ 2)) := by
          gcongr; exact hw_bound ζ
      _ = bound ζ := by simp only [bound]; ring
  have hhas : HasFDerivAt (fun q => ∫ ζ : ℝ × ℝ, F q ζ) (∫ ζ : ℝ × ℝ, F' p ζ) p := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds p (half_pos hp))
    · exact Eventually.of_forall hF_meas
    · exact hF_int
    · exact hF'_meas
    · exact Eventually.of_forall hF'_bound
    · exact hbound_int
    · exact Eventually.of_forall fun ζ q _ => by
        simpa only [F, F', smul_smul] using (hasFDerivAt_expMode (-(sommerfeldRoot k ζ.1 ζ.2)) ζ.1 ζ.2 q).const_mul (w ζ)
  rw [pd, hhas.fderiv]
  have hF'_int : Integrable (F' p) volume :=
    Integrable.mono' hbound_int hF'_meas (Eventually.of_forall fun ζ => hF'_bound ζ p (Metric.mem_ball_self (half_pos hp)))
  have happly : (∫ ζ : ℝ × ℝ, F' p ζ) (EuclideanSpace.single i (1 : ℝ)) =
      ∫ ζ : ℝ × ℝ, F' p ζ (EuclideanSpace.single i (1 : ℝ)) :=
    ((ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single i (1 : ℝ))).integral_comp_comm hF'_int).symm
  rw [happly]
  congr 1; ext ζ
  have hproj : ∀ (k' j : Fin 3),
      EuclideanSpace.proj (𝕜 := ℝ) k' (EuclideanSpace.single j (1 : ℝ)) = if k' = j then 1 else 0 := by
    intro k' j; change (EuclideanSpace.single j (1 : ℝ)).ofLp k' = _; simp [PiLp.single_apply]
  have hghat_p : ghat k ζ.1 ζ.2 0 * Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (p 2 : ℂ)) =
      ghat k ζ.1 ζ.2 (p 2) := by
    simp only [ghat, abs_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, abs_of_pos hp]
    ring
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, F', w, FunLike.coe_smul,
      Pi.smul_apply, FunLike.coe_add, Pi.add_apply,
      ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, hproj, mode, smul_eq_mul,
      ↓reduceIte, Fin.isValue, Fin.reduceEq, Complex.ofReal_one, Complex.ofReal_zero,
      mul_one, mul_zero, add_zero, zero_add] <;>
    (rw [← hghat_p]; ring)

theorem solution (ω : ℝ) (ε μ k : ℂ) (hkdef : k = wavenumber ω ε μ)
    (hk : IsCausalWavenumber k) (J : Space → Fin 3 → ℂ) (ρ : Space → ℂ) (hJ : ContDiff ℝ 1 J)
    (hJc : HasCompactSupport J) (hJV : tsupport J ⊆ {q : Space | q 2 < 0})
    (hcont : ∀ q, divergence J q = Complex.I * ω * ρ q) (p : Space) (hp : 0 < p 2) :
    lorenzE ω ε μ J p 2 = ∫ ζ : ℝ × ℝ, ghat k ζ.1 ζ.2 (p 2) *
        (∫ q : Space, Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) *
          (Complex.I * ω * μ * J q 2 + sommerfeldRoot k ζ.1 ζ.2 / ε * ρ q) *
          Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1)))) *
        planeWave ζ.1 ζ.2 (p 0) (p 1) := by
  have hJ_cont : Continuous J := hJ.continuous
  have hJ2_cont : Continuous (fun q => J q 2) := (continuous_apply 2).comp hJ_cont
  have hJ2_supp : tsupport (fun q => J q 2) ⊆ tsupport J :=
    closure_mono fun q hq => by intro h0; apply hq; simp [h0]
  have hJ2_comp : HasCompactSupport (fun q => J q 2) :=
    hJc.comp_left (g := fun v : Fin 3 → ℂ => v 2) rfl
  have hJ2_V : tsupport (fun q => J q 2) ⊆ {q : Space | q 2 < 0} := hJ2_supp.trans hJV
  have hdiv_cont : Continuous (divergence J) := by
    have hpd_cont : ∀ i : Fin 3, Continuous (fun q => pd i (fun r => J r i) q) := fun i => by
      have hJi : ContDiff ℝ 1 (fun r => J r i) := contDiff_pi.mp hJ i
      exact (ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single i (1 : ℝ))).continuous.comp
        (hJi.continuous_fderiv (by simp))
    unfold divergence
    exact ((hpd_cont 0).add (hpd_cont 1)).add (hpd_cont 2)
  have hdiv_supp : tsupport (divergence J) ⊆ tsupport J := by
    apply closure_minimal _ (isClosed_tsupport J)
    intro q hq
    by_contra hq_not
    have hopen : IsOpen (tsupport J)ᶜ := (isClosed_tsupport J).isOpen_compl
    have hev0 : ∀ i : Fin 3, (fun r => J r i) =ᶠ[𝓝 q] (fun _ => (0 : ℂ)) := fun i => by
      filter_upwards [hopen.mem_nhds hq_not] with r hr
      have hJr : J r = 0 := image_eq_zero_of_notMem_tsupport hr
      simp [hJr]
    have hpd0 : ∀ i : Fin 3, pd i (fun r => J r i) q = 0 := fun i => by
      simp [pd, (hev0 i).fderiv_eq]
    apply hq
    simp [divergence, hpd0]
  have hdiv_comp : HasCompactSupport (divergence J) :=
    hJc.isCompact.of_isClosed_subset (isClosed_tsupport _) hdiv_supp
  have hdiv_V : tsupport (divergence J) ⊆ {q : Space | q 2 < 0} := hdiv_supp.trans hJV
  have hk_ne : k ≠ 0 := by
    intro h0; have := hk.1; rw [h0, Complex.zero_re] at this; exact lt_irrefl 0 this
  have hω_ne : (ω : ℂ) ≠ 0 := by
    intro h0; apply hk_ne; rw [hkdef, wavenumber, h0, zero_mul]
  have hε_ne : ε ≠ 0 := by
    intro h0; apply hk_ne; rw [hkdef, wavenumber, h0, zero_mul, Complex.zero_cpow (by norm_num), mul_zero]
  -- Expand lorenzE ω ε μ J p 2 using volumePotential_eq_spectral and pd_volumePotential_spectral
  unfold lorenzE vectorPotential grad
  rw [← hkdef]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  rw [volumePotential_eq_spectral k hk (fun q => J q 2) hJ2_cont hJ2_comp hJ2_V p hp,
      pd_volumePotential_spectral k hk (divergence J) hdiv_cont hdiv_comp hdiv_V p hp 2]
  -- Helper: integrability of weighted spectral terms
  have hint_term : ∀ (f : Space → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
      (hfV : tsupport f ⊆ {q : Space | q 2 < 0}) (c : ℝ × ℝ → ℂ) (hcm : Measurable c)
      (M : ℝ) (hM : 0 ≤ M) (hc : ∀ ζ : ℝ × ℝ, ‖c ζ‖ ≤ M * (1 + ζ.1 ^ 2 + ζ.2 ^ 2)),
      Integrable (fun ζ : ℝ × ℝ => c ζ * ghat k ζ.1 ζ.2 (p 2) *
        (∫ q : Space, Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) * f q *
          Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1)))) *
        planeWave ζ.1 ζ.2 (p 0) (p 1)) volume := by
    intro f hf hfc hfV c hcm M hM hc
    have hinner_m : StronglyMeasurable (fun ζ : ℝ × ℝ =>
        ∫ q : Space, Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) * f q *
          Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1)))) := by
      apply StronglyMeasurable.integral_prod_right
      have hβ : Measurable (fun x : (ℝ × ℝ) × Space => sommerfeldRoot k x.1.1 x.1.2) :=
        (measurable_sommerfeldRoot k).comp measurable_fst
      have hf' : Measurable (fun x : (ℝ × ℝ) × Space => f x.2) := hf.measurable.comp measurable_snd
      have hq0 : Measurable (fun x : (ℝ × ℝ) × Space => ((x.2 0 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.measurable.comp ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).continuous.measurable.comp measurable_snd)
      have hq1 : Measurable (fun x : (ℝ × ℝ) × Space => ((x.2 1 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.measurable.comp ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).continuous.measurable.comp measurable_snd)
      have hq2 : Measurable (fun x : (ℝ × ℝ) × Space => ((x.2 2 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.measurable.comp ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.measurable.comp measurable_snd)
      have hexp1 : Measurable (fun x : (ℝ × ℝ) × Space => Complex.exp (sommerfeldRoot k x.1.1 x.1.2 * x.2 2)) :=
        Complex.continuous_exp.measurable.comp (hβ.mul hq2)
      have hexp2 : Measurable (fun x : (ℝ × ℝ) × Space =>
          Complex.exp (-(Complex.I * ((x.1.1 : ℂ) * (x.2 0 : ℂ) + (x.1.2 : ℂ) * (x.2 1 : ℂ))))) :=
        Complex.continuous_exp.measurable.comp
          ((measurable_const.mul
            (((Complex.continuous_ofReal.measurable.comp (measurable_fst.comp measurable_fst)).mul hq0).add
             ((Complex.continuous_ofReal.measurable.comp (measurable_snd.comp measurable_fst)).mul hq1))).neg)
      exact ((hexp1.mul hf').mul hexp2).stronglyMeasurable
    have hpw_m : Measurable (fun ζ : ℝ × ℝ => planeWave ζ.1 ζ.2 (p 0) (p 1)) := by unfold planeWave; fun_prop
    have hmeas : AEStronglyMeasurable (fun ζ : ℝ × ℝ => c ζ * ghat k ζ.1 ζ.2 (p 2) *
        (∫ q : Space, Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) * f q *
          Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1)))) *
        planeWave ζ.1 ζ.2 (p 0) (p 1)) volume :=
      (((hcm.aestronglyMeasurable.mul (measurable_ghat k (p 2)).aestronglyMeasurable).mul
        hinner_m.aestronglyMeasurable).mul hpw_m.aestronglyMeasurable)
    set Cf : ℝ := ∫ q : Space, ‖f q‖
    have hpoly : Integrable (fun ζ : ℝ × ℝ => (1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 (p 2)‖) volume := by
      simpa using integrable_ghat_poly k hk (p 2) hp 1
    refine Integrable.mono' (hpoly.const_mul (M * Cf)) hmeas (Eventually.of_forall fun ζ => ?_)
    have hinner_le : ‖∫ q : Space, Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) * f q *
        Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1)))‖ ≤ Cf := by
      calc _ ≤ ∫ q : Space, ‖Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) * f q *
              Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1)))‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ q : Space, ‖f q‖ := by
            apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
              (hf.integrable_of_hasCompactSupport hfc).norm
            refine Eventually.of_forall fun q => ?_
            by_cases hfq : f q = 0
            · simp [hfq]
            · have hq_neg : q 2 < 0 := hfV (subset_tsupport _ hfq)
              have hexp1 : ‖Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * (q 2 : ℂ))‖ ≤ 1 := by
                rw [Complex.norm_exp]; apply Real.exp_le_one_iff.mpr
                have hre : (sommerfeldRoot k ζ.1 ζ.2 * (q 2 : ℂ)).re = (sommerfeldRoot k ζ.1 ζ.2).re * q 2 := by simp
                rw [hre]; nlinarith [sommerfeldRoot_re_nonneg k ζ.1 ζ.2]
              have hexp2 : ‖Complex.exp (-(Complex.I * ((ζ.1 : ℂ) * (q 0 : ℂ) + (ζ.2 : ℂ) * (q 1 : ℂ))))‖ = 1 := by
                have : -(Complex.I * ((ζ.1 : ℂ) * (q 0 : ℂ) + (ζ.2 : ℂ) * (q 1 : ℂ))) =
                    ((-(ζ.1 * q 0 + ζ.2 * q 1) : ℝ) : ℂ) * Complex.I := by push_cast; ring
                rw [this, Complex.norm_exp_ofReal_mul_I]
              dsimp only
              rw [norm_mul, norm_mul, hexp2, mul_one]
              exact (mul_le_mul_of_nonneg_right hexp1 (norm_nonneg _)).trans (by rw [one_mul])
    simp only [norm_mul, norm_planeWave, mul_one]
    calc ‖c ζ‖ * ‖ghat k ζ.1 ζ.2 (p 2)‖ * _
        ≤ (M * (1 + ζ.1 ^ 2 + ζ.2 ^ 2)) * ‖ghat k ζ.1 ζ.2 (p 2)‖ * Cf := by gcongr; exact hc ζ
      _ = M * Cf * ((1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 (p 2)‖) := by ring
  -- Pull constants into the two outer integrals
  have h1_pull : (Complex.I * (ω : ℂ) * μ) *
      (∫ ζ : ℝ × ℝ, ghat k ζ.1 ζ.2 (p 2) *
        (∫ q : Space, Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) * J q 2 *
          Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1)))) *
        planeWave ζ.1 ζ.2 (p 0) (p 1)) =
      ∫ ζ : ℝ × ℝ, (Complex.I * (ω : ℂ) * μ) * ghat k ζ.1 ζ.2 (p 2) *
        (∫ q : Space, Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) * J q 2 *
          Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1)))) *
        planeWave ζ.1 ζ.2 (p 0) (p 1) := by
    rw [← integral_const_mul]; congr 1; ext ζ; ring
  have h2_pull : (1 / (Complex.I * (ω : ℂ) * ε)) *
      (∫ ζ : ℝ × ℝ, -(sommerfeldRoot k ζ.1 ζ.2) * ghat k ζ.1 ζ.2 (p 2) *
        (∫ q : Space, Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) * divergence J q *
          Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1)))) *
        planeWave ζ.1 ζ.2 (p 0) (p 1)) =
      ∫ ζ : ℝ × ℝ, ((1 / (Complex.I * (ω : ℂ) * ε)) * -(sommerfeldRoot k ζ.1 ζ.2)) * ghat k ζ.1 ζ.2 (p 2) *
        (∫ q : Space, Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) * divergence J q *
          Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1)))) *
        planeWave ζ.1 ζ.2 (p 0) (p 1) := by
    rw [← integral_const_mul]; congr 1; ext ζ; ring
  rw [h1_pull, h2_pull]
  have hint1 := hint_term (fun q => J q 2) hJ2_cont hJ2_comp hJ2_V
    (fun _ => Complex.I * (ω : ℂ) * μ) measurable_const ‖Complex.I * (ω : ℂ) * μ‖ (norm_nonneg _)
    (fun ζ => by
      have hge1 : 1 ≤ 1 + ζ.1 ^ 2 + ζ.2 ^ 2 := by nlinarith [sq_nonneg ζ.1, sq_nonneg ζ.2]
      calc ‖Complex.I * (ω : ℂ) * μ‖ = ‖Complex.I * (ω : ℂ) * μ‖ * 1 := (mul_one _).symm
        _ ≤ ‖Complex.I * (ω : ℂ) * μ‖ * (1 + ζ.1 ^ 2 + ζ.2 ^ 2) := by gcongr)
  have hint2 := hint_term (divergence J) hdiv_cont hdiv_comp hdiv_V
    (fun ζ => (1 / (Complex.I * (ω : ℂ) * ε)) * -(sommerfeldRoot k ζ.1 ζ.2))
    (measurable_const.mul (measurable_sommerfeldRoot k).neg)
    (‖1 / (Complex.I * (ω : ℂ) * ε)‖ * (1 + ‖k‖)) (by positivity)
    (fun ζ => by
      rw [norm_mul, norm_neg]
      have hsqrt_le : Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2) ≤ 1 + ζ.1 ^ 2 + ζ.2 ^ 2 :=
        Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [sq_nonneg ζ.1, sq_nonneg ζ.2]⟩
      have hβle : ‖sommerfeldRoot k ζ.1 ζ.2‖ ≤ (1 + ‖k‖) * (1 + ζ.1 ^ 2 + ζ.2 ^ 2) :=
        (norm_sommerfeldRoot_le k ζ.1 ζ.2).trans (by gcongr)
      calc ‖1 / (Complex.I * (ω : ℂ) * ε)‖ * ‖sommerfeldRoot k ζ.1 ζ.2‖
          ≤ ‖1 / (Complex.I * (ω : ℂ) * ε)‖ * ((1 + ‖k‖) * (1 + ζ.1 ^ 2 + ζ.2 ^ 2)) := by gcongr
        _ = ‖1 / (Complex.I * (ω : ℂ) * ε)‖ * (1 + ‖k‖) * (1 + ζ.1 ^ 2 + ζ.2 ^ 2) := by ring)
  rw [← MeasureTheory.integral_sub hint1 hint2]
  congr 1; ext ζ
  have hint_q : ∀ (f : Space → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
      (hfV : tsupport f ⊆ {q : Space | q 2 < 0}),
      Integrable (fun q : Space =>
        Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) * f q *
          Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1)))) volume := by
    intro f hf hfc hfV
    refine Integrable.mono' (hf.integrable_of_hasCompactSupport hfc).norm ?_
      (Eventually.of_forall fun q => ?_)
    · have hq0 : Continuous (fun q : Space => ((q 0 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).continuous
      have hq1 : Continuous (fun q : Space => ((q 1 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).continuous
      have hq2 : Continuous (fun q : Space => ((q 2 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous
      exact (((Complex.continuous_exp.comp (continuous_const.mul hq2)).mul hf).mul
        (Complex.continuous_exp.comp ((continuous_const.mul ((continuous_const.mul hq0).add (continuous_const.mul hq1))).neg))).aestronglyMeasurable
    · by_cases hfq : f q = 0
      · simp [hfq]
      · have hq_neg : q 2 < 0 := hfV (subset_tsupport _ hfq)
        have hexp1 : ‖Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * (q 2 : ℂ))‖ ≤ 1 := by
          rw [Complex.norm_exp]; apply Real.exp_le_one_iff.mpr
          have hre : (sommerfeldRoot k ζ.1 ζ.2 * (q 2 : ℂ)).re = (sommerfeldRoot k ζ.1 ζ.2).re * q 2 := by simp
          rw [hre]; nlinarith [sommerfeldRoot_re_nonneg k ζ.1 ζ.2]
        have hexp2 : ‖Complex.exp (-(Complex.I * ((ζ.1 : ℂ) * (q 0 : ℂ) + (ζ.2 : ℂ) * (q 1 : ℂ))))‖ = 1 := by
          have : -(Complex.I * ((ζ.1 : ℂ) * (q 0 : ℂ) + (ζ.2 : ℂ) * (q 1 : ℂ))) =
              ((-(ζ.1 * q 0 + ζ.2 * q 1) : ℝ) : ℂ) * Complex.I := by push_cast; ring
          rw [this, Complex.norm_exp_ofReal_mul_I]
        rw [norm_mul, norm_mul, hexp2, mul_one]
        exact (mul_le_mul_of_nonneg_right hexp1 (norm_nonneg _)).trans (by rw [one_mul])
  have hq_comb :
      (Complex.I * (ω : ℂ) * μ) *
        (∫ q : Space, Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) * J q 2 *
          Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1)))) -
      ((1 / (Complex.I * (ω : ℂ) * ε)) * -(sommerfeldRoot k ζ.1 ζ.2)) *
        (∫ q : Space, Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) * divergence J q *
          Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1)))) =
      ∫ q : Space, Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) *
        (Complex.I * (ω : ℂ) * μ * J q 2 + sommerfeldRoot k ζ.1 ζ.2 / ε * ρ q) *
        Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1))) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← MeasureTheory.integral_sub
        ((hint_q (fun q => J q 2) hJ2_cont hJ2_comp hJ2_V).const_mul _)
        ((hint_q (divergence J) hdiv_cont hdiv_comp hdiv_V).const_mul _)]
    congr 1; ext q
    rw [hcont q]
    field_simp [Complex.I_ne_zero, hω_ne, hε_ne]
    ring
  rw [← hq_comb]; ring
