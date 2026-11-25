-- Prove2me | solution 1 for Arxiv1310_4241.mie_tangential_boundary_values
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T19:54:19.713349+00:00
-- url     : https://prove2.me/submissions/05f265d6-d9ea-4cc8-8d7c-10fe84518dbb

import Mathlib
import Definitions.Def_Arxiv1310_4241_Basic

open MeasureTheory Filter Topology Arxiv1310_4241

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

private lemma norm_sommerfeldRoot_sq (k : ℂ) (ξ η : ℝ) :
    ‖sommerfeldRoot k ξ η‖ ^ 2 ≤ ξ ^ 2 + η ^ 2 + ‖k‖ ^ 2 := by
  have h1 : ‖sommerfeldRoot k ξ η‖ ^ 2 = ‖(ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2‖ := by
    rw [← norm_pow, sommerfeldRoot_sq]
  rw [h1]
  have h2 : ‖(ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2‖ ≤ ‖(ξ : ℂ) ^ 2 + (η : ℂ) ^ 2‖ + ‖k ^ 2‖ :=
    norm_sub_le _ _
  have h3 : ‖(ξ : ℂ) ^ 2 + (η : ℂ) ^ 2‖ = ξ ^ 2 + η ^ 2 := by
    have : (ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 = ((ξ ^ 2 + η ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [h3, norm_pow] at h2
  exact h2

private lemma norm_sommerfeldRoot_le (k : ℂ) (ξ η : ℝ) :
    ‖sommerfeldRoot k ξ η‖ ≤ (1 + ‖k‖) * Real.sqrt (1 + ξ ^ 2 + η ^ 2) := by
  have h1 := norm_sommerfeldRoot_sq k ξ η
  have h2 : ‖sommerfeldRoot k ξ η‖ ^ 2 ≤ ((1 + ‖k‖) * Real.sqrt (1 + ξ ^ 2 + η ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith [norm_nonneg k, sq_nonneg ξ, sq_nonneg η]
  exact le_of_sq_le_sq h2 (by positivity)

private lemma norm_exp_neg_sommerfeldRoot_le_one (k : ℂ) (ξ η z : ℝ) (hz : 0 ≤ z) :
    ‖Complex.exp (-(sommerfeldRoot k ξ η) * (z : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  apply Real.exp_le_one_iff.mpr
  have hre : (-(sommerfeldRoot k ξ η) * (z : ℂ)).re = -(sommerfeldRoot k ξ η).re * z := by
    simp
  rw [hre]
  nlinarith [sommerfeldRoot_re_nonneg k ξ η]

private lemma norm_mode_eq_one (ξ η : ℝ) (p : Space) : ‖mode ξ η p‖ = 1 := by
  simp only [mode, planeWave]
  have : Complex.I * ((ξ : ℂ) * (p 0 : ℂ) + (η : ℂ) * (p 1 : ℂ)) =
      (((ξ * p 0 + η * p 1 : ℝ) : ℂ) * Complex.I) := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

private lemma measurable_sommerfeldRoot (k : ℂ) :
    Measurable (fun ζ : ℝ × ℝ => sommerfeldRoot k ζ.1 ζ.2) := by
  unfold sommerfeldRoot
  have hf : Measurable (fun ζ : ℝ × ℝ => (ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 - k ^ 2) := by
    fun_prop
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

/-- Differentiation under the integral sign on `upperHalfSpace` for spectral integrals
`p ↦ ∫ ζ, w ζ * (exp (-β(ζ) p_z) * mode ζ.1 ζ.2 p)`. -/
private lemma pd_modeIntegral (k : ℂ) (w : ℝ × ℝ → ℂ)
    (hwm : AEStronglyMeasurable w volume)
    (hw0 : Integrable (fun ζ : ℝ × ℝ => ‖w ζ‖))
    (hw1 : Integrable (fun ζ : ℝ × ℝ => (|ζ.1| + |ζ.2| + ‖sommerfeldRoot k ζ.1 ζ.2‖) * ‖w ζ‖))
    (p : Space) (hp : 0 < p 2) :
    ∀ i : Fin 3,
      pd i (fun q => ∫ ζ : ℝ × ℝ, w ζ * (Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (q 2 : ℂ)) * mode ζ.1 ζ.2 q)) p =
        ∫ ζ : ℝ × ℝ,
          (match i with | 0 => Complex.I * ζ.1 | 1 => Complex.I * ζ.2 | 2 => -(sommerfeldRoot k ζ.1 ζ.2)) *
            w ζ * (Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (p 2 : ℂ)) * mode ζ.1 ζ.2 p) := by
  let F : Space → ℝ × ℝ → ℂ := fun q ζ =>
    w ζ * (Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (q 2 : ℂ)) * mode ζ.1 ζ.2 q)
  let F' : Space → ℝ × ℝ → Space →L[ℝ] ℂ := fun q ζ =>
    (w ζ * (Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (q 2 : ℂ)) * mode ζ.1 ζ.2 q)) •
      (-(sommerfeldRoot k ζ.1 ζ.2) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3))) +
        Complex.I • ((ζ.1 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3))) +
          (ζ.2 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)))))
  let bound : ℝ × ℝ → ℝ := fun ζ => (|ζ.1| + |ζ.2| + ‖sommerfeldRoot k ζ.1 ζ.2‖) * ‖w ζ‖
  have hproj_norm : ∀ j : Fin 3, ‖Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) j)‖ ≤ 1 := by
    intro j
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real, one_mul]
    exact PiLp.norm_apply_le v j
  have hF_meas : ∀ q : Space, AEStronglyMeasurable (F q) volume := by
    intro q
    have hβ := measurable_sommerfeldRoot k
    have hmode : Measurable (fun ζ : ℝ × ℝ =>
        Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (q 2 : ℂ)) * mode ζ.1 ζ.2 q) := by
      unfold mode planeWave
      exact (Complex.continuous_exp.measurable.comp ((hβ.neg).mul measurable_const)).mul
        (Complex.continuous_exp.measurable.comp
          (measurable_const.mul
            (((Complex.continuous_ofReal.measurable.comp measurable_fst).mul measurable_const).add
              ((Complex.continuous_ofReal.measurable.comp measurable_snd).mul measurable_const))))
    exact hwm.mul hmode.aestronglyMeasurable
  have hF_int : Integrable (F p) volume := by
    refine Integrable.mono' hw0 (hF_meas p) (Eventually.of_forall fun ζ => ?_)
    simp only [F, norm_mul, norm_mode_eq_one, mul_one]
    calc ‖w ζ‖ * ‖Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (p 2 : ℂ))‖
        ≤ ‖w ζ‖ * 1 := mul_le_mul_of_nonneg_left (norm_exp_neg_sommerfeldRoot_le_one k ζ.1 ζ.2 (p 2) hp.le) (norm_nonneg _)
      _ = ‖w ζ‖ := mul_one _
  have hF'_meas : AEStronglyMeasurable (F' p) volume := by
    have hβ := measurable_sommerfeldRoot k
    have h1 : AEStronglyMeasurable (fun ζ : ℝ × ℝ => F p ζ) volume := hF_meas p
    have hL : Measurable (fun ζ : ℝ × ℝ =>
        ((-(sommerfeldRoot k ζ.1 ζ.2) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3))) +
          Complex.I • ((ζ.1 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3))) +
            (ζ.2 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3))))) : Space →L[ℝ] ℂ)) := by
      have hm2 : Measurable (fun ζ : ℝ × ℝ =>
          (-(sommerfeldRoot k ζ.1 ζ.2) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3))) : Space →L[ℝ] ℂ)) :=
        (hβ.neg).smul measurable_const
      have hm0 : Measurable (fun ζ : ℝ × ℝ =>
          ((ζ.1 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3))) : Space →L[ℝ] ℂ)) :=
        (Complex.continuous_ofReal.measurable.comp measurable_fst).smul measurable_const
      have hm1 : Measurable (fun ζ : ℝ × ℝ =>
          ((ζ.2 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3))) : Space →L[ℝ] ℂ)) :=
        (Complex.continuous_ofReal.measurable.comp measurable_snd).smul measurable_const
      exact hm2.add ((hm0.add hm1).const_smul Complex.I)
    exact h1.smul hL.aestronglyMeasurable
  have hF'_bound : ∀ q ∈ Metric.ball p (p 2 / 2), ∀ ζ : ℝ × ℝ, ‖F' q ζ‖ ≤ bound ζ := by
    intro q hq ζ
    have hq2 : 0 ≤ q 2 := by
      have hd : ‖q - p‖ < p 2 / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hq
      have hcoord : |q 2 - p 2| ≤ ‖q - p‖ := by
        simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (q - p) (2 : Fin 3)
      linarith [(abs_le.mp (hcoord.trans hd.le)).1]
    simp only [F', norm_smul, norm_mul, norm_mode_eq_one, mul_one]
    have hexp_le := norm_exp_neg_sommerfeldRoot_le_one k ζ.1 ζ.2 (q 2) hq2
    have hL_le : ‖-(sommerfeldRoot k ζ.1 ζ.2) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3))) +
          Complex.I • ((ζ.1 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3))) +
            (ζ.2 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3))))‖ ≤
        |ζ.1| + |ζ.2| + ‖sommerfeldRoot k ζ.1 ζ.2‖ := by
      calc ‖-(sommerfeldRoot k ζ.1 ζ.2) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3))) +
            Complex.I • ((ζ.1 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3))) +
              (ζ.2 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3))))‖
          ≤ ‖-(sommerfeldRoot k ζ.1 ζ.2) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)))‖ +
            ‖Complex.I • ((ζ.1 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3))) +
              (ζ.2 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3))))‖ := norm_add_le _ _
        _ ≤ ‖sommerfeldRoot k ζ.1 ζ.2‖ * 1 +
            1 * (|ζ.1| * 1 + |ζ.2| * 1) := by
            gcongr
            · rw [norm_smul, norm_neg]; exact mul_le_mul_of_nonneg_left (hproj_norm 2) (norm_nonneg _)
            · rw [norm_smul, Complex.norm_I, one_mul, one_mul]
              calc ‖(ζ.1 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3))) +
                    (ζ.2 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)))‖
                  ≤ ‖(ζ.1 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)))‖ +
                    ‖(ζ.2 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)))‖ := norm_add_le _ _
                _ ≤ |ζ.1| * 1 + |ζ.2| * 1 := by
                    gcongr
                    · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hproj_norm 0) (abs_nonneg _)
                    · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hproj_norm 1) (abs_nonneg _)
        _ = |ζ.1| + |ζ.2| + ‖sommerfeldRoot k ζ.1 ζ.2‖ := by ring
    calc ‖w ζ‖ * ‖Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (q 2 : ℂ))‖ *
            ‖-(sommerfeldRoot k ζ.1 ζ.2) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3))) +
              Complex.I • ((ζ.1 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3))) +
                (ζ.2 : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3))))‖
        ≤ (‖w ζ‖ * 1) * (|ζ.1| + |ζ.2| + ‖sommerfeldRoot k ζ.1 ζ.2‖) := by
          gcongr
      _ = bound ζ := by simp only [bound]; ring
  have hhas : HasFDerivAt (fun q => ∫ ζ : ℝ × ℝ, F q ζ) (∫ ζ : ℝ × ℝ, F' p ζ) p := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds p (half_pos hp))
    · exact Eventually.of_forall hF_meas
    · exact hF_int
    · exact hF'_meas
    · exact Eventually.of_forall fun ζ q hq => hF'_bound q hq ζ
    · exact hw1
    · exact Eventually.of_forall fun ζ q _ => by
        simpa only [F, F', smul_smul] using (hasFDerivAt_expMode (-(sommerfeldRoot k ζ.1 ζ.2)) ζ.1 ζ.2 q).const_mul (w ζ)
  intro i
  rw [pd, hhas.fderiv]
  have hF'_int : Integrable (F' p) volume :=
    Integrable.mono' hw1 hF'_meas (Eventually.of_forall fun ζ => hF'_bound p (Metric.mem_ball_self (half_pos hp)) ζ)
  have happly : (∫ ζ : ℝ × ℝ, F' p ζ) (EuclideanSpace.single i (1 : ℝ)) =
      ∫ ζ : ℝ × ℝ, F' p ζ (EuclideanSpace.single i (1 : ℝ)) :=
    ((ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single i (1 : ℝ))).integral_comp_comm hF'_int).symm
  rw [happly]
  congr 1; ext ζ
  have hproj : ∀ (k' j : Fin 3),
      EuclideanSpace.proj (𝕜 := ℝ) k' (EuclideanSpace.single j (1 : ℝ)) = if k' = j then 1 else 0 := by
    intro k' j; change (EuclideanSpace.single j (1 : ℝ)).ofLp k' = _; simp [PiLp.single_apply]
  fin_cases i <;> simp [F', hproj] <;> ring

private lemma debyePotential_eq_modeIntegral (k : ℂ) (σh : ℝ × ℝ → ℂ) {q : Space} (hq : 0 < q 2) :
    debyePotential k σh q =
      ∫ ζ : ℝ × ℝ, (ghat k ζ.1 ζ.2 0 * σh ζ) *
        (Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (q 2 : ℂ)) * mode ζ.1 ζ.2 q) := by
  unfold debyePotential
  congr 1; ext ζ
  simp only [ghat, mode, abs_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, abs_of_pos hq]
  ring

private lemma integrable_weight_of_hσ (k : ℂ) (σh : ℝ × ℝ → ℂ)
    (hσm : AEStronglyMeasurable σh volume)
    (hσ : Integrable (fun ζ : ℝ × ℝ => (1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖))
    (g : ℝ × ℝ → ℂ) (hgm : Measurable g) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ ζ : ℝ × ℝ, ‖g ζ‖ ≤ C * (1 + ζ.1 ^ 2 + ζ.2 ^ 2)) :
    Integrable (fun ζ : ℝ × ℝ => ‖g ζ * (ghat k ζ.1 ζ.2 0 * σh ζ)‖) := by
  have hghat_m : Measurable (fun ζ : ℝ × ℝ => ghat k ζ.1 ζ.2 0) := by
    simp only [ghat, abs_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    exact measurable_const.div (measurable_const.mul (measurable_sommerfeldRoot k))
  have hmeas : AEStronglyMeasurable (fun ζ : ℝ × ℝ => ‖g ζ * (ghat k ζ.1 ζ.2 0 * σh ζ)‖) volume :=
    (hgm.aestronglyMeasurable.mul (hghat_m.aestronglyMeasurable.mul hσm)).norm
  refine Integrable.mono' (hσ.const_mul C) hmeas (Eventually.of_forall fun ζ => ?_)
  rw [Real.norm_of_nonneg (norm_nonneg _), norm_mul, norm_mul]
  calc ‖g ζ‖ * (‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖)
      ≤ (C * (1 + ζ.1 ^ 2 + ζ.2 ^ 2)) * (‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖) :=
        mul_le_mul_of_nonneg_right (hg ζ) (by positivity)
    _ = C * ((1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖) := by ring

private lemma integrable_deriv_weight_of_hσ (k : ℂ) (σh : ℝ × ℝ → ℂ)
    (hσm : AEStronglyMeasurable σh volume)
    (hσ : Integrable (fun ζ : ℝ × ℝ => (1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖))
    (g : ℝ × ℝ → ℂ) (hgm : Measurable g) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ ζ : ℝ × ℝ, (|ζ.1| + |ζ.2| + ‖sommerfeldRoot k ζ.1 ζ.2‖) * ‖g ζ‖ ≤ C * (1 + ζ.1 ^ 2 + ζ.2 ^ 2)) :
    Integrable (fun ζ : ℝ × ℝ => (|ζ.1| + |ζ.2| + ‖sommerfeldRoot k ζ.1 ζ.2‖) * ‖g ζ * (ghat k ζ.1 ζ.2 0 * σh ζ)‖) := by
  have hghat_m : Measurable (fun ζ : ℝ × ℝ => ghat k ζ.1 ζ.2 0) := by
    simp only [ghat, abs_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    exact measurable_const.div (measurable_const.mul (measurable_sommerfeldRoot k))
  have hβ_m : Measurable (fun ζ : ℝ × ℝ => ‖sommerfeldRoot k ζ.1 ζ.2‖) :=
    (measurable_sommerfeldRoot k).norm
  have hfac_m : Measurable (fun ζ : ℝ × ℝ => |ζ.1| + |ζ.2| + ‖sommerfeldRoot k ζ.1 ζ.2‖) :=
    ((measurable_fst.abs).add (measurable_snd.abs)).add hβ_m
  have hmeas : AEStronglyMeasurable
      (fun ζ : ℝ × ℝ => (|ζ.1| + |ζ.2| + ‖sommerfeldRoot k ζ.1 ζ.2‖) * ‖g ζ * (ghat k ζ.1 ζ.2 0 * σh ζ)‖) volume :=
    hfac_m.aestronglyMeasurable.mul (hgm.aestronglyMeasurable.mul (hghat_m.aestronglyMeasurable.mul hσm)).norm
  refine Integrable.mono' (hσ.const_mul C) hmeas (Eventually.of_forall fun ζ => ?_)
  have hnn : 0 ≤ |ζ.1| + |ζ.2| + ‖sommerfeldRoot k ζ.1 ζ.2‖ := by positivity
  rw [Real.norm_of_nonneg (mul_nonneg hnn (norm_nonneg _)), norm_mul, norm_mul]
  calc (|ζ.1| + |ζ.2| + ‖sommerfeldRoot k ζ.1 ζ.2‖) * (‖g ζ‖ * (‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖))
      = ((|ζ.1| + |ζ.2| + ‖sommerfeldRoot k ζ.1 ζ.2‖) * ‖g ζ‖) * (‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖) := by ring
    _ ≤ (C * (1 + ζ.1 ^ 2 + ζ.2 ^ 2)) * (‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖) :=
        mul_le_mul_of_nonneg_right (hg ζ) (by positivity)
    _ = C * ((1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖) := by ring

theorem solution (ω : ℝ) (ε μ k : ℂ) (hkdef : k = wavenumber ω ε μ)
    (hk : IsCausalWavenumber k) (σh τh : ℝ × ℝ → ℂ)
    (hσm : AEStronglyMeasurable σh volume) (hτm : AEStronglyMeasurable τh volume)
    (hσ : Integrable (fun ζ : ℝ × ℝ => (1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖))
    (hτ : Integrable (fun ζ : ℝ × ℝ => (1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖τh ζ‖))
    (x y : ℝ) :
    Tendsto (fun z => mieE ω μ (debyePotential k σh) (debyePotential k τh) (pt x y z) 0)
      (𝓝[>] 0) (𝓝 (∫ ζ : ℝ × ℝ, ghat k ζ.1 ζ.2 0 *
        (-(Complex.I * ζ.1 * sommerfeldRoot k ζ.1 ζ.2 * σh ζ) - ω * μ * ζ.2 * τh ζ) *
        planeWave ζ.1 ζ.2 x y)) ∧
    Tendsto (fun z => mieE ω μ (debyePotential k σh) (debyePotential k τh) (pt x y z) 1)
      (𝓝[>] 0) (𝓝 (∫ ζ : ℝ × ℝ, ghat k ζ.1 ζ.2 0 *
        (-(Complex.I * ζ.2 * sommerfeldRoot k ζ.1 ζ.2 * σh ζ) + ω * μ * ζ.1 * τh ζ) *
        planeWave ζ.1 ζ.2 x y)) ∧
    Tendsto (fun z => mieE ω μ (debyePotential k σh) (debyePotential k τh) (pt x y z) 2)
      (𝓝[>] 0) (𝓝 (∫ ζ : ℝ × ℝ, ghat k ζ.1 ζ.2 0 * ((ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2) * σh ζ *
        planeWave ζ.1 ζ.2 x y)) := by
  have isOpen_uhs : IsOpen upperHalfSpace :=
    isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous
  have hghat_m : Measurable (fun ζ : ℝ × ℝ => ghat k ζ.1 ζ.2 0) := by
    simp only [ghat, abs_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    exact measurable_const.div (measurable_const.mul (measurable_sommerfeldRoot k))
  -- Elementary polynomial bounds
  have hfac_bound : ∀ ζ : ℝ × ℝ, |ζ.1| + |ζ.2| + ‖sommerfeldRoot k ζ.1 ζ.2‖ ≤
      (3 + ‖k‖) * Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2) := by
    intro ζ
    have h1 : |ζ.1| ≤ Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ζ.2])
    have h2 : |ζ.2| ≤ Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ζ.1])
    have h3 := norm_sommerfeldRoot_le k ζ.1 ζ.2
    linarith
  have hsqrt_le : ∀ ζ : ℝ × ℝ, Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2) ≤ 1 + ζ.1 ^ 2 + ζ.2 ^ 2 := by
    intro ζ
    have hge : 1 ≤ 1 + ζ.1 ^ 2 + ζ.2 ^ 2 := by nlinarith [sq_nonneg ζ.1, sq_nonneg ζ.2]
    exact Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  -- First partials of debyePotential on upperHalfSpace
  have hpd_debye : ∀ (ρh : ℝ × ℝ → ℂ) (hρm : AEStronglyMeasurable ρh volume)
      (hρ : Integrable (fun ζ : ℝ × ℝ => (1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖ρh ζ‖))
      (p : Space) (hp : 0 < p 2) (i : Fin 3),
      pd i (debyePotential k ρh) p =
        ∫ ζ : ℝ × ℝ,
          (match i with | 0 => Complex.I * ζ.1 | 1 => Complex.I * ζ.2 | 2 => -(sommerfeldRoot k ζ.1 ζ.2)) *
            (ghat k ζ.1 ζ.2 0 * ρh ζ) * (Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (p 2 : ℂ)) * mode ζ.1 ζ.2 p) := by
    intro ρh hρm hρ p hp i
    have hev : debyePotential k ρh =ᶠ[𝓝 p]
        fun q => ∫ ζ : ℝ × ℝ, (ghat k ζ.1 ζ.2 0 * ρh ζ) *
          (Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (q 2 : ℂ)) * mode ζ.1 ζ.2 q) := by
      filter_upwards [isOpen_uhs.mem_nhds hp] with q hq
      exact debyePotential_eq_modeIntegral k ρh hq
    rw [pd, hev.fderiv_eq]
    change pd i _ p = _
    apply pd_modeIntegral k (fun ζ => ghat k ζ.1 ζ.2 0 * ρh ζ)
      (hghat_m.aestronglyMeasurable.mul hρm)
    · simpa using integrable_weight_of_hσ k ρh hρm hρ (fun _ => 1) measurable_const 1 zero_le_one
        (fun ζ => by simp; nlinarith [sq_nonneg ζ.1, sq_nonneg ζ.2])
    · simpa using integrable_deriv_weight_of_hσ k ρh hρm hρ (fun _ => 1) measurable_const (3 + ‖k‖) (by positivity)
        (fun ζ => by
          simp only [norm_one, mul_one]
          exact (hfac_bound ζ).trans (mul_le_mul_of_nonneg_left (hsqrt_le ζ) (by positivity)))
    · exact hp
  -- Second partials of u = debyePotential k σh on upperHalfSpace
  have hpd2_u : ∀ (j i : Fin 3) (hj : j = 0 ∨ j = 1) (p : Space) (hp : 0 < p 2),
      pd i (pd j (debyePotential k σh)) p =
        ∫ ζ : ℝ × ℝ,
          (match i with | 0 => Complex.I * ζ.1 | 1 => Complex.I * ζ.2 | 2 => -(sommerfeldRoot k ζ.1 ζ.2)) *
          ((match j with | 0 => Complex.I * ζ.1 | 1 => Complex.I * ζ.2 | 2 => -(sommerfeldRoot k ζ.1 ζ.2)) *
            (ghat k ζ.1 ζ.2 0 * σh ζ)) *
          (Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (p 2 : ℂ)) * mode ζ.1 ζ.2 p) := by
    intro j i hj p hp
    let g : ℝ × ℝ → ℂ := fun ζ =>
      match j with | 0 => Complex.I * ζ.1 | 1 => Complex.I * ζ.2 | 2 => -(sommerfeldRoot k ζ.1 ζ.2)
    have hgm : Measurable g := by
      rcases hj with rfl | rfl
      · exact measurable_const.mul (Complex.continuous_ofReal.measurable.comp measurable_fst)
      · exact measurable_const.mul (Complex.continuous_ofReal.measurable.comp measurable_snd)
    have hgnorm : ∀ ζ : ℝ × ℝ, ‖g ζ‖ ≤ Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2) := by
      intro ζ
      rcases hj with rfl | rfl
      · simp only [g, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ζ.2])
      · simp only [g, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ζ.1])
    have hev : pd j (debyePotential k σh) =ᶠ[𝓝 p]
        fun q => ∫ ζ : ℝ × ℝ, (g ζ * (ghat k ζ.1 ζ.2 0 * σh ζ)) *
          (Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (q 2 : ℂ)) * mode ζ.1 ζ.2 q) := by
      filter_upwards [isOpen_uhs.mem_nhds hp] with q hq
      rw [hpd_debye σh hσm hσ q hq j]
      congr 1; ext ζ; rcases hj with rfl | rfl <;> rfl
    rw [pd, hev.fderiv_eq]
    change pd i _ p = _
    apply pd_modeIntegral k (fun ζ => g ζ * (ghat k ζ.1 ζ.2 0 * σh ζ))
      (hgm.aestronglyMeasurable.mul (hghat_m.aestronglyMeasurable.mul hσm))
    · exact integrable_weight_of_hσ k σh hσm hσ g hgm 1 zero_le_one
        (fun ζ => by simpa using (hgnorm ζ).trans (hsqrt_le ζ))
    · exact integrable_deriv_weight_of_hσ k σh hσm hσ g hgm (3 + ‖k‖) (by positivity)
        (fun ζ => by
          calc (|ζ.1| + |ζ.2| + ‖sommerfeldRoot k ζ.1 ζ.2‖) * ‖g ζ‖
              ≤ ((3 + ‖k‖) * Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2)) * Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2) :=
                mul_le_mul (hfac_bound ζ) (hgnorm ζ) (norm_nonneg _) (by positivity)
            _ = (3 + ‖k‖) * (1 + ζ.1 ^ 2 + ζ.2 ^ 2) := by
                rw [mul_assoc, Real.mul_self_sqrt (by positivity)])
    · exact hp
  -- Explicit formulas for mieE components on upperHalfSpace
  have hcurl_zhat : ∀ (f : Space → ℂ) (p : Space), curl (zhatField f) p = ![pd 1 f p, -pd 0 f p, 0] := by
    intro f p; ext i; fin_cases i <;> simp [curl, zhatField, pd]
  have hcurl_curl_zhat : ∀ (f : Space → ℂ) (p : Space),
      curl (curl (zhatField f)) p =
        ![pd 2 (pd 0 f) p, pd 2 (pd 1 f) p, -(pd 0 (pd 0 f) p + pd 1 (pd 1 f) p)] := by
    intro f p
    have hcz : curl (zhatField f) = fun q => ![pd 1 f q, -pd 0 f q, 0] := by
      ext q i; exact congrFun (hcurl_zhat f q) i
    have hpd_neg : ∀ (i : Fin 3) (g : Space → ℂ), pd i (fun q => -g q) p = -pd i g p := fun i g => by
      simp [pd, fderiv_fun_neg]
    rw [hcz]; ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, curl, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, hpd_neg]
      simp [pd]
    · simp only [Fin.mk_one, Fin.isValue, curl, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      have h0 : pd 0 (fun _ : Space => (0 : ℂ)) p = 0 := by simp [pd]
      rw [h0, sub_zero]
    · simp only [Fin.reduceFinMk, Fin.isValue, curl, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, hpd_neg]
      ring
  -- Helper: dominated convergence as z → 0⁺ for spectral integrals
  have htendsto_mode : ∀ (Φ : ℝ × ℝ → ℂ) (hΦm : AEStronglyMeasurable Φ volume)
      (B : ℝ × ℝ → ℝ) (hB : Integrable B volume)
      (hΦB : ∀ ζ : ℝ × ℝ, ‖Φ ζ‖ ≤ B ζ),
      Tendsto (fun z : ℝ => ∫ ζ : ℝ × ℝ,
          Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ)) * Φ ζ * planeWave ζ.1 ζ.2 x y)
        (𝓝[>] 0) (𝓝 (∫ ζ : ℝ × ℝ, Φ ζ * planeWave ζ.1 ζ.2 x y)) := by
    intro Φ hΦm B hB hΦB
    have hpw_m : Measurable (fun ζ : ℝ × ℝ => planeWave ζ.1 ζ.2 x y) := by
      unfold planeWave
      exact Complex.continuous_exp.measurable.comp
        (measurable_const.mul
          (((Complex.continuous_ofReal.measurable.comp measurable_fst).mul measurable_const).add
            ((Complex.continuous_ofReal.measurable.comp measurable_snd).mul measurable_const)))
    have hpw_norm : ∀ ζ : ℝ × ℝ, ‖planeWave ζ.1 ζ.2 x y‖ = 1 := fun ζ => by
      simpa [mode, pt] using norm_mode_eq_one ζ.1 ζ.2 (pt x y 0)
    apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence B
    · exact Eventually.of_forall fun z =>
        ((Complex.continuous_exp.measurable.comp
          (((measurable_sommerfeldRoot k).neg).mul measurable_const)).aestronglyMeasurable.mul hΦm).mul
          hpw_m.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with z hz
      refine Eventually.of_forall fun ζ => ?_
      rw [norm_mul, norm_mul, hpw_norm, mul_one]
      calc ‖Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ))‖ * ‖Φ ζ‖
          ≤ 1 * B ζ := mul_le_mul (norm_exp_neg_sommerfeldRoot_le_one k ζ.1 ζ.2 z (le_of_lt hz))
              (hΦB ζ) (norm_nonneg _) zero_le_one
        _ = B ζ := one_mul _
    · exact hB
    · refine Eventually.of_forall fun ζ => ?_
      have hc : Continuous (fun z : ℝ => Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ)) * Φ ζ * planeWave ζ.1 ζ.2 x y) := by
        fun_prop
      have h0 : Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * ((0 : ℝ) : ℂ)) * Φ ζ * planeWave ζ.1 ζ.2 x y =
          Φ ζ * planeWave ζ.1 ζ.2 x y := by simp
      rw [← h0]
      exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  -- Integrability helpers for each term at z > 0
  have hint_u20 : ∀ z : ℝ, 0 < z → Integrable (fun ζ : ℝ × ℝ =>
      -(sommerfeldRoot k ζ.1 ζ.2) * (Complex.I * ζ.1 * (ghat k ζ.1 ζ.2 0 * σh ζ)) *
        (Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ)) * planeWave ζ.1 ζ.2 x y)) := by
    intro z hz
    have hmeas : AEStronglyMeasurable (fun ζ : ℝ × ℝ =>
        -(sommerfeldRoot k ζ.1 ζ.2) * (Complex.I * ζ.1 * (ghat k ζ.1 ζ.2 0 * σh ζ)) *
          (Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ)) * planeWave ζ.1 ζ.2 x y)) volume := by
      have hm1 : Measurable (fun ζ : ℝ × ℝ => -(sommerfeldRoot k ζ.1 ζ.2)) := (measurable_sommerfeldRoot k).neg
      have hm2 : Measurable (fun ζ : ℝ × ℝ => Complex.I * (ζ.1 : ℂ)) :=
        measurable_const.mul (Complex.continuous_ofReal.measurable.comp measurable_fst)
      have hm3 : Measurable (fun ζ : ℝ × ℝ => Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ)) * planeWave ζ.1 ζ.2 x y) := by
        unfold planeWave
        exact (Complex.continuous_exp.measurable.comp (hm1.mul measurable_const)).mul
          (Complex.continuous_exp.measurable.comp (measurable_const.mul
            (((Complex.continuous_ofReal.measurable.comp measurable_fst).mul measurable_const).add
              ((Complex.continuous_ofReal.measurable.comp measurable_snd).mul measurable_const))))
      exact (hm1.aestronglyMeasurable.mul (hm2.aestronglyMeasurable.mul (hghat_m.aestronglyMeasurable.mul hσm))).mul
        hm3.aestronglyMeasurable
    refine Integrable.mono' (hσ.const_mul (1 + ‖k‖)) hmeas (Eventually.of_forall fun ζ => ?_)
    have hpw : ‖planeWave ζ.1 ζ.2 x y‖ = 1 := by simpa [mode, pt] using norm_mode_eq_one ζ.1 ζ.2 (pt x y 0)
    simp only [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, hpw, mul_one]
    have h1 := norm_sommerfeldRoot_le k ζ.1 ζ.2
    have h2 : |ζ.1| ≤ Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ζ.2])
    have h3 := norm_exp_neg_sommerfeldRoot_le_one k ζ.1 ζ.2 z hz.le
    calc ‖sommerfeldRoot k ζ.1 ζ.2‖ * (|ζ.1| * (‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖)) *
            ‖Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ))‖
        ≤ ((1 + ‖k‖) * Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2)) *
            (Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2) * (‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖)) * 1 := by gcongr
      _ = (1 + ‖k‖) * ((Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2) * Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2)) *
            ‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖) := by ring
      _ = (1 + ‖k‖) * ((1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖) := by
          rw [Real.mul_self_sqrt (by positivity)]
  have hint_u21 : ∀ z : ℝ, 0 < z → Integrable (fun ζ : ℝ × ℝ =>
      -(sommerfeldRoot k ζ.1 ζ.2) * (Complex.I * ζ.2 * (ghat k ζ.1 ζ.2 0 * σh ζ)) *
        (Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ)) * planeWave ζ.1 ζ.2 x y)) := by
    intro z hz
    have hmeas : AEStronglyMeasurable (fun ζ : ℝ × ℝ =>
        -(sommerfeldRoot k ζ.1 ζ.2) * (Complex.I * ζ.2 * (ghat k ζ.1 ζ.2 0 * σh ζ)) *
          (Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ)) * planeWave ζ.1 ζ.2 x y)) volume := by
      have hm1 : Measurable (fun ζ : ℝ × ℝ => -(sommerfeldRoot k ζ.1 ζ.2)) := (measurable_sommerfeldRoot k).neg
      have hm2 : Measurable (fun ζ : ℝ × ℝ => Complex.I * (ζ.2 : ℂ)) :=
        measurable_const.mul (Complex.continuous_ofReal.measurable.comp measurable_snd)
      have hm3 : Measurable (fun ζ : ℝ × ℝ => Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ)) * planeWave ζ.1 ζ.2 x y) := by
        unfold planeWave
        exact (Complex.continuous_exp.measurable.comp (hm1.mul measurable_const)).mul
          (Complex.continuous_exp.measurable.comp (measurable_const.mul
            (((Complex.continuous_ofReal.measurable.comp measurable_fst).mul measurable_const).add
              ((Complex.continuous_ofReal.measurable.comp measurable_snd).mul measurable_const))))
      exact (hm1.aestronglyMeasurable.mul (hm2.aestronglyMeasurable.mul (hghat_m.aestronglyMeasurable.mul hσm))).mul
        hm3.aestronglyMeasurable
    refine Integrable.mono' (hσ.const_mul (1 + ‖k‖)) hmeas (Eventually.of_forall fun ζ => ?_)
    have hpw : ‖planeWave ζ.1 ζ.2 x y‖ = 1 := by simpa [mode, pt] using norm_mode_eq_one ζ.1 ζ.2 (pt x y 0)
    simp only [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, hpw, mul_one]
    have h1 := norm_sommerfeldRoot_le k ζ.1 ζ.2
    have h2 : |ζ.2| ≤ Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ζ.1])
    have h3 := norm_exp_neg_sommerfeldRoot_le_one k ζ.1 ζ.2 z hz.le
    calc ‖sommerfeldRoot k ζ.1 ζ.2‖ * (|ζ.2| * (‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖)) *
            ‖Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ))‖
        ≤ ((1 + ‖k‖) * Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2)) *
            (Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2) * (‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖)) * 1 := by gcongr
      _ = (1 + ‖k‖) * ((Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2) * Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2)) *
            ‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖) := by ring
      _ = (1 + ‖k‖) * ((1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖) := by
          rw [Real.mul_self_sqrt (by positivity)]
  have hint_v1 : ∀ z : ℝ, 0 < z → Integrable (fun ζ : ℝ × ℝ =>
      (Complex.I * (ω : ℂ) * μ) * ((Complex.I * ζ.2) * (ghat k ζ.1 ζ.2 0 * τh ζ) *
        (Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ)) * planeWave ζ.1 ζ.2 x y))) := by
    intro z hz
    have hmeas : AEStronglyMeasurable (fun ζ : ℝ × ℝ =>
        (Complex.I * (ω : ℂ) * μ) * ((Complex.I * ζ.2) * (ghat k ζ.1 ζ.2 0 * τh ζ) *
          (Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ)) * planeWave ζ.1 ζ.2 x y))) volume := by
      have hm1 : Measurable (fun ζ : ℝ × ℝ => -(sommerfeldRoot k ζ.1 ζ.2)) := (measurable_sommerfeldRoot k).neg
      have hm2 : Measurable (fun ζ : ℝ × ℝ => Complex.I * (ζ.2 : ℂ)) :=
        measurable_const.mul (Complex.continuous_ofReal.measurable.comp measurable_snd)
      have hm3 : Measurable (fun ζ : ℝ × ℝ => Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ)) * planeWave ζ.1 ζ.2 x y) := by
        unfold planeWave
        exact (Complex.continuous_exp.measurable.comp (hm1.mul measurable_const)).mul
          (Complex.continuous_exp.measurable.comp (measurable_const.mul
            (((Complex.continuous_ofReal.measurable.comp measurable_fst).mul measurable_const).add
              ((Complex.continuous_ofReal.measurable.comp measurable_snd).mul measurable_const))))
      exact measurable_const.aestronglyMeasurable.mul
        ((hm2.aestronglyMeasurable.mul (hghat_m.aestronglyMeasurable.mul hτm)).mul hm3.aestronglyMeasurable)
    refine Integrable.mono' (hτ.const_mul ‖(ω : ℂ) * μ‖) hmeas (Eventually.of_forall fun ζ => ?_)
    have hpw : ‖planeWave ζ.1 ζ.2 x y‖ = 1 := by simpa [mode, pt] using norm_mode_eq_one ζ.1 ζ.2 (pt x y 0)
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, hpw, mul_one]
    have h2 : |ζ.2| ≤ 1 + ζ.1 ^ 2 + ζ.2 ^ 2 := by
      have : |ζ.2| ≤ Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2) := by
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ζ.1])
      exact this.trans (hsqrt_le ζ)
    have h3 := norm_exp_neg_sommerfeldRoot_le_one k ζ.1 ζ.2 z hz.le
    calc |ω| * ‖μ‖ * (|ζ.2| * (‖ghat k ζ.1 ζ.2 0‖ * ‖τh ζ‖) *
            ‖Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ))‖)
        ≤ |ω| * ‖μ‖ * ((1 + ζ.1 ^ 2 + ζ.2 ^ 2) * (‖ghat k ζ.1 ζ.2 0‖ * ‖τh ζ‖) * 1) := by gcongr
      _ = |ω| * ‖μ‖ * ((1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖τh ζ‖) := by ring
  have hint_v0 : ∀ z : ℝ, 0 < z → Integrable (fun ζ : ℝ × ℝ =>
      (-(Complex.I * (ω : ℂ) * μ)) * ((Complex.I * ζ.1) * (ghat k ζ.1 ζ.2 0 * τh ζ) *
        (Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ)) * planeWave ζ.1 ζ.2 x y))) := by
    intro z hz
    have hmeas : AEStronglyMeasurable (fun ζ : ℝ × ℝ =>
        (-(Complex.I * (ω : ℂ) * μ)) * ((Complex.I * ζ.1) * (ghat k ζ.1 ζ.2 0 * τh ζ) *
          (Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ)) * planeWave ζ.1 ζ.2 x y))) volume := by
      have hm1 : Measurable (fun ζ : ℝ × ℝ => -(sommerfeldRoot k ζ.1 ζ.2)) := (measurable_sommerfeldRoot k).neg
      have hm2 : Measurable (fun ζ : ℝ × ℝ => Complex.I * (ζ.1 : ℂ)) :=
        measurable_const.mul (Complex.continuous_ofReal.measurable.comp measurable_fst)
      have hm3 : Measurable (fun ζ : ℝ × ℝ => Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ)) * planeWave ζ.1 ζ.2 x y) := by
        unfold planeWave
        exact (Complex.continuous_exp.measurable.comp (hm1.mul measurable_const)).mul
          (Complex.continuous_exp.measurable.comp (measurable_const.mul
            (((Complex.continuous_ofReal.measurable.comp measurable_fst).mul measurable_const).add
              ((Complex.continuous_ofReal.measurable.comp measurable_snd).mul measurable_const))))
      exact measurable_const.aestronglyMeasurable.mul
        ((hm2.aestronglyMeasurable.mul (hghat_m.aestronglyMeasurable.mul hτm)).mul hm3.aestronglyMeasurable)
    refine Integrable.mono' (hτ.const_mul ‖(ω : ℂ) * μ‖) hmeas (Eventually.of_forall fun ζ => ?_)
    have hpw : ‖planeWave ζ.1 ζ.2 x y‖ = 1 := by simpa [mode, pt] using norm_mode_eq_one ζ.1 ζ.2 (pt x y 0)
    simp only [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, hpw, mul_one]
    have h2 : |ζ.1| ≤ 1 + ζ.1 ^ 2 + ζ.2 ^ 2 := by
      have : |ζ.1| ≤ Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2) := by
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ζ.2])
      exact this.trans (hsqrt_le ζ)
    have h3 := norm_exp_neg_sommerfeldRoot_le_one k ζ.1 ζ.2 z hz.le
    calc |ω| * ‖μ‖ * (|ζ.1| * (‖ghat k ζ.1 ζ.2 0‖ * ‖τh ζ‖) *
            ‖Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ))‖)
        ≤ |ω| * ‖μ‖ * ((1 + ζ.1 ^ 2 + ζ.2 ^ 2) * (‖ghat k ζ.1 ζ.2 0‖ * ‖τh ζ‖) * 1) := by gcongr
      _ = |ω| * ‖μ‖ * ((1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖τh ζ‖) := by ring
  have hint_u00 : ∀ z : ℝ, 0 < z → Integrable (fun ζ : ℝ × ℝ =>
      (Complex.I * ζ.1) * ((Complex.I * ζ.1) * (ghat k ζ.1 ζ.2 0 * σh ζ)) *
        (Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ)) * planeWave ζ.1 ζ.2 x y)) := by
    intro z hz
    have hmeas : AEStronglyMeasurable (fun ζ : ℝ × ℝ =>
        (Complex.I * ζ.1) * ((Complex.I * ζ.1) * (ghat k ζ.1 ζ.2 0 * σh ζ)) *
          (Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ)) * planeWave ζ.1 ζ.2 x y)) volume := by
      have hm1 : Measurable (fun ζ : ℝ × ℝ => -(sommerfeldRoot k ζ.1 ζ.2)) := (measurable_sommerfeldRoot k).neg
      have hm2 : Measurable (fun ζ : ℝ × ℝ => Complex.I * (ζ.1 : ℂ)) :=
        measurable_const.mul (Complex.continuous_ofReal.measurable.comp measurable_fst)
      have hm3 : Measurable (fun ζ : ℝ × ℝ => Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ)) * planeWave ζ.1 ζ.2 x y) := by
        unfold planeWave
        exact (Complex.continuous_exp.measurable.comp (hm1.mul measurable_const)).mul
          (Complex.continuous_exp.measurable.comp (measurable_const.mul
            (((Complex.continuous_ofReal.measurable.comp measurable_fst).mul measurable_const).add
              ((Complex.continuous_ofReal.measurable.comp measurable_snd).mul measurable_const))))
      exact (hm2.aestronglyMeasurable.mul (hm2.aestronglyMeasurable.mul (hghat_m.aestronglyMeasurable.mul hσm))).mul
        hm3.aestronglyMeasurable
    refine Integrable.mono' hσ hmeas (Eventually.of_forall fun ζ => ?_)
    have hpw : ‖planeWave ζ.1 ζ.2 x y‖ = 1 := by simpa [mode, pt] using norm_mode_eq_one ζ.1 ζ.2 (pt x y 0)
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, hpw, mul_one]
    have h3 := norm_exp_neg_sommerfeldRoot_le_one k ζ.1 ζ.2 z hz.le
    calc |ζ.1| * (|ζ.1| * (‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖)) *
            ‖Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ))‖
        ≤ (1 + ζ.1 ^ 2 + ζ.2 ^ 2) * (‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖) * 1 := by
          have hsq : |ζ.1| * |ζ.1| ≤ 1 + ζ.1 ^ 2 + ζ.2 ^ 2 := by
            rw [abs_mul_abs_self]; nlinarith [sq_nonneg ζ.2]
          have h1 : |ζ.1| * (|ζ.1| * (‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖)) ≤
              (1 + ζ.1 ^ 2 + ζ.2 ^ 2) * (‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖) := by
            rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hsq (by positivity)
          exact mul_le_mul h1 h3 (norm_nonneg _) (by positivity)
      _ = (1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖ := by ring
  have hint_u11 : ∀ z : ℝ, 0 < z → Integrable (fun ζ : ℝ × ℝ =>
      (Complex.I * ζ.2) * ((Complex.I * ζ.2) * (ghat k ζ.1 ζ.2 0 * σh ζ)) *
        (Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ)) * planeWave ζ.1 ζ.2 x y)) := by
    intro z hz
    have hmeas : AEStronglyMeasurable (fun ζ : ℝ × ℝ =>
        (Complex.I * ζ.2) * ((Complex.I * ζ.2) * (ghat k ζ.1 ζ.2 0 * σh ζ)) *
          (Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ)) * planeWave ζ.1 ζ.2 x y)) volume := by
      have hm1 : Measurable (fun ζ : ℝ × ℝ => -(sommerfeldRoot k ζ.1 ζ.2)) := (measurable_sommerfeldRoot k).neg
      have hm2 : Measurable (fun ζ : ℝ × ℝ => Complex.I * (ζ.2 : ℂ)) :=
        measurable_const.mul (Complex.continuous_ofReal.measurable.comp measurable_snd)
      have hm3 : Measurable (fun ζ : ℝ × ℝ => Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ)) * planeWave ζ.1 ζ.2 x y) := by
        unfold planeWave
        exact (Complex.continuous_exp.measurable.comp (hm1.mul measurable_const)).mul
          (Complex.continuous_exp.measurable.comp (measurable_const.mul
            (((Complex.continuous_ofReal.measurable.comp measurable_fst).mul measurable_const).add
              ((Complex.continuous_ofReal.measurable.comp measurable_snd).mul measurable_const))))
      exact (hm2.aestronglyMeasurable.mul (hm2.aestronglyMeasurable.mul (hghat_m.aestronglyMeasurable.mul hσm))).mul
        hm3.aestronglyMeasurable
    refine Integrable.mono' hσ hmeas (Eventually.of_forall fun ζ => ?_)
    have hpw : ‖planeWave ζ.1 ζ.2 x y‖ = 1 := by simpa [mode, pt] using norm_mode_eq_one ζ.1 ζ.2 (pt x y 0)
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, hpw, mul_one]
    have h3 := norm_exp_neg_sommerfeldRoot_le_one k ζ.1 ζ.2 z hz.le
    calc |ζ.2| * (|ζ.2| * (‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖)) *
            ‖Complex.exp (-(sommerfeldRoot k ζ.1 ζ.2) * (z : ℂ))‖
        ≤ (1 + ζ.1 ^ 2 + ζ.2 ^ 2) * (‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖) * 1 := by
          have hsq : |ζ.2| * |ζ.2| ≤ 1 + ζ.1 ^ 2 + ζ.2 ^ 2 := by
            rw [abs_mul_abs_self]; nlinarith [sq_nonneg ζ.1]
          have h1 : |ζ.2| * (|ζ.2| * (‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖)) ≤
              (1 + ζ.1 ^ 2 + ζ.2 ^ 2) * (‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖) := by
            rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hsq (by positivity)
          exact mul_le_mul h1 h3 (norm_nonneg _) (by positivity)
      _ = (1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖ := by ring
  -- Now prove the three Tendsto statements
  refine ⟨?_, ?_, ?_⟩
  · -- Component 0
    let Φ0 : ℝ × ℝ → ℂ := fun ζ =>
      ghat k ζ.1 ζ.2 0 * (-(Complex.I * ζ.1 * sommerfeldRoot k ζ.1 ζ.2 * σh ζ) - ω * μ * ζ.2 * τh ζ)
    have hΦ0m : AEStronglyMeasurable Φ0 volume := by
      have hm1 : Measurable (fun ζ : ℝ × ℝ => Complex.I * (ζ.1 : ℂ) * sommerfeldRoot k ζ.1 ζ.2) :=
        (measurable_const.mul (Complex.continuous_ofReal.measurable.comp measurable_fst)).mul (measurable_sommerfeldRoot k)
      have hm2 : Measurable (fun ζ : ℝ × ℝ => (ω : ℂ) * μ * (ζ.2 : ℂ)) :=
        measurable_const.mul (Complex.continuous_ofReal.measurable.comp measurable_snd)
      exact hghat_m.aestronglyMeasurable.mul
        ((hm1.aestronglyMeasurable.mul hσm).neg.sub (hm2.aestronglyMeasurable.mul hτm))
    let B0 : ℝ × ℝ → ℝ := fun ζ =>
      (1 + ‖k‖) * ((1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖) +
      ‖(ω : ℂ) * μ‖ * ((1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖τh ζ‖)
    have hB0 : Integrable B0 volume := (hσ.const_mul (1 + ‖k‖)).add (hτ.const_mul ‖(ω : ℂ) * μ‖)
    have hΦ0B : ∀ ζ, ‖Φ0 ζ‖ ≤ B0 ζ := by
      intro ζ
      simp only [Φ0, norm_mul]
      calc ‖ghat k ζ.1 ζ.2 0‖ * ‖-(Complex.I * ↑ζ.1 * sommerfeldRoot k ζ.1 ζ.2 * σh ζ) - ↑ω * μ * ↑ζ.2 * τh ζ‖
          ≤ ‖ghat k ζ.1 ζ.2 0‖ * (‖-(Complex.I * ↑ζ.1 * sommerfeldRoot k ζ.1 ζ.2 * σh ζ)‖ + ‖↑ω * μ * ↑ζ.2 * τh ζ‖) :=
            mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
        _ ≤ B0 ζ := by
            simp only [B0, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
            have h1 := norm_sommerfeldRoot_le k ζ.1 ζ.2
            have hx : |ζ.1| ≤ Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2) := by
              rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ζ.2])
            have hy : |ζ.2| ≤ 1 + ζ.1 ^ 2 + ζ.2 ^ 2 := by
              have hy0 : |ζ.2| ≤ Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2) := by
                rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ζ.1])
              exact hy0.trans (hsqrt_le ζ)
            have hprod1 : |ζ.1| * ‖sommerfeldRoot k ζ.1 ζ.2‖ ≤ (1 + ‖k‖) * (1 + ζ.1 ^ 2 + ζ.2 ^ 2) := by
              calc |ζ.1| * ‖sommerfeldRoot k ζ.1 ζ.2‖
                  ≤ Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ((1 + ‖k‖) * Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2)) :=
                    mul_le_mul hx h1 (norm_nonneg _) (Real.sqrt_nonneg _)
                _ = (1 + ‖k‖) * (Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2) * Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2)) := by ring
                _ = (1 + ‖k‖) * (1 + ζ.1 ^ 2 + ζ.2 ^ 2) := by rw [Real.mul_self_sqrt (by positivity)]
            have ht1 : ‖ghat k ζ.1 ζ.2 0‖ * (|ζ.1| * ‖sommerfeldRoot k ζ.1 ζ.2‖ * ‖σh ζ‖) ≤
                (1 + ‖k‖) * ((1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖) := by
              calc ‖ghat k ζ.1 ζ.2 0‖ * (|ζ.1| * ‖sommerfeldRoot k ζ.1 ζ.2‖ * ‖σh ζ‖)
                  ≤ ‖ghat k ζ.1 ζ.2 0‖ * (((1 + ‖k‖) * (1 + ζ.1 ^ 2 + ζ.2 ^ 2)) * ‖σh ζ‖) := by gcongr
                _ = (1 + ‖k‖) * ((1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖) := by ring
            have ht2 : ‖ghat k ζ.1 ζ.2 0‖ * (|ω| * ‖μ‖ * |ζ.2| * ‖τh ζ‖) ≤
                |ω| * ‖μ‖ * ((1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖τh ζ‖) := by
              calc ‖ghat k ζ.1 ζ.2 0‖ * (|ω| * ‖μ‖ * |ζ.2| * ‖τh ζ‖)
                  ≤ ‖ghat k ζ.1 ζ.2 0‖ * (|ω| * ‖μ‖ * (1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖τh ζ‖) := by gcongr
                _ = |ω| * ‖μ‖ * ((1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖τh ζ‖) := by ring
            linarith
    refine (htendsto_mode Φ0 hΦ0m B0 hB0 hΦ0B).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hpt2 : (pt x y z) 2 = z := by simp [pt]
    have hmode : ∀ ζ : ℝ × ℝ, mode ζ.1 ζ.2 (pt x y z) = planeWave ζ.1 ζ.2 x y := fun ζ => by simp [mode, pt]
    simp only [mieE, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hcurl_curl_zhat, hcurl_zhat,
      Matrix.cons_val_zero]
    rw [hpd2_u 0 2 (Or.inl rfl) (pt x y z) (by rw [hpt2]; exact hz),
        hpd_debye τh hτm hτ (pt x y z) (by rw [hpt2]; exact hz) 1]
    simp only [hpt2, hmode]
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_add (hint_u20 z hz) (hint_v1 z hz)]
    congr 1; ext ζ
    simp only [Φ0]
    ring_nf; simp [Complex.I_sq]; ring
  · -- Component 1
    let Φ1 : ℝ × ℝ → ℂ := fun ζ =>
      ghat k ζ.1 ζ.2 0 * (-(Complex.I * ζ.2 * sommerfeldRoot k ζ.1 ζ.2 * σh ζ) + ω * μ * ζ.1 * τh ζ)
    have hΦ1m : AEStronglyMeasurable Φ1 volume := by
      have hm1 : Measurable (fun ζ : ℝ × ℝ => Complex.I * (ζ.2 : ℂ) * sommerfeldRoot k ζ.1 ζ.2) :=
        (measurable_const.mul (Complex.continuous_ofReal.measurable.comp measurable_snd)).mul (measurable_sommerfeldRoot k)
      have hm2 : Measurable (fun ζ : ℝ × ℝ => (ω : ℂ) * μ * (ζ.1 : ℂ)) :=
        measurable_const.mul (Complex.continuous_ofReal.measurable.comp measurable_fst)
      exact hghat_m.aestronglyMeasurable.mul
        ((hm1.aestronglyMeasurable.mul hσm).neg.add (hm2.aestronglyMeasurable.mul hτm))
    let B1 : ℝ × ℝ → ℝ := fun ζ =>
      (1 + ‖k‖) * ((1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖) +
      ‖(ω : ℂ) * μ‖ * ((1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖τh ζ‖)
    have hB1 : Integrable B1 volume := (hσ.const_mul (1 + ‖k‖)).add (hτ.const_mul ‖(ω : ℂ) * μ‖)
    have hΦ1B : ∀ ζ, ‖Φ1 ζ‖ ≤ B1 ζ := by
      intro ζ
      simp only [Φ1, norm_mul]
      calc ‖ghat k ζ.1 ζ.2 0‖ * ‖-(Complex.I * ↑ζ.2 * sommerfeldRoot k ζ.1 ζ.2 * σh ζ) + ↑ω * μ * ↑ζ.1 * τh ζ‖
          ≤ ‖ghat k ζ.1 ζ.2 0‖ * (‖-(Complex.I * ↑ζ.2 * sommerfeldRoot k ζ.1 ζ.2 * σh ζ)‖ + ‖↑ω * μ * ↑ζ.1 * τh ζ‖) :=
            mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
        _ ≤ B1 ζ := by
            simp only [B1, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
            have h1 := norm_sommerfeldRoot_le k ζ.1 ζ.2
            have hy : |ζ.2| ≤ Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2) := by
              rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ζ.1])
            have hx : |ζ.1| ≤ 1 + ζ.1 ^ 2 + ζ.2 ^ 2 := by
              have hx0 : |ζ.1| ≤ Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2) := by
                rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ζ.2])
              exact hx0.trans (hsqrt_le ζ)
            have hprod1 : |ζ.2| * ‖sommerfeldRoot k ζ.1 ζ.2‖ ≤ (1 + ‖k‖) * (1 + ζ.1 ^ 2 + ζ.2 ^ 2) := by
              calc |ζ.2| * ‖sommerfeldRoot k ζ.1 ζ.2‖
                  ≤ Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ((1 + ‖k‖) * Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2)) :=
                    mul_le_mul hy h1 (norm_nonneg _) (Real.sqrt_nonneg _)
                _ = (1 + ‖k‖) * (Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2) * Real.sqrt (1 + ζ.1 ^ 2 + ζ.2 ^ 2)) := by ring
                _ = (1 + ‖k‖) * (1 + ζ.1 ^ 2 + ζ.2 ^ 2) := by rw [Real.mul_self_sqrt (by positivity)]
            have ht1 : ‖ghat k ζ.1 ζ.2 0‖ * (|ζ.2| * ‖sommerfeldRoot k ζ.1 ζ.2‖ * ‖σh ζ‖) ≤
                (1 + ‖k‖) * ((1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖) := by
              calc ‖ghat k ζ.1 ζ.2 0‖ * (|ζ.2| * ‖sommerfeldRoot k ζ.1 ζ.2‖ * ‖σh ζ‖)
                  ≤ ‖ghat k ζ.1 ζ.2 0‖ * (((1 + ‖k‖) * (1 + ζ.1 ^ 2 + ζ.2 ^ 2)) * ‖σh ζ‖) := by gcongr
                _ = (1 + ‖k‖) * ((1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖) := by ring
            have ht2 : ‖ghat k ζ.1 ζ.2 0‖ * (|ω| * ‖μ‖ * |ζ.1| * ‖τh ζ‖) ≤
                |ω| * ‖μ‖ * ((1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖τh ζ‖) := by
              calc ‖ghat k ζ.1 ζ.2 0‖ * (|ω| * ‖μ‖ * |ζ.1| * ‖τh ζ‖)
                  ≤ ‖ghat k ζ.1 ζ.2 0‖ * (|ω| * ‖μ‖ * (1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖τh ζ‖) := by gcongr
                _ = |ω| * ‖μ‖ * ((1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖τh ζ‖) := by ring
            linarith
    refine (htendsto_mode Φ1 hΦ1m B1 hB1 hΦ1B).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hpt2 : (pt x y z) 2 = z := by simp [pt]
    have hmode : ∀ ζ : ℝ × ℝ, mode ζ.1 ζ.2 (pt x y z) = planeWave ζ.1 ζ.2 x y := fun ζ => by simp [mode, pt]
    simp only [mieE, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hcurl_curl_zhat, hcurl_zhat,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [hpd2_u 1 2 (Or.inr rfl) (pt x y z) (by rw [hpt2]; exact hz),
        hpd_debye τh hτm hτ (pt x y z) (by rw [hpt2]; exact hz) 0]
    simp only [hpt2, hmode]
    rw [show (Complex.I * ↑ω * μ) * -(∫ ζ : ℝ × ℝ, _) =
        (-(Complex.I * ↑ω * μ)) * (∫ ζ : ℝ × ℝ, _) by ring]
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_add (hint_u21 z hz) (hint_v0 z hz)]
    congr 1; ext ζ
    simp only [Φ1]
    ring_nf; simp [Complex.I_sq]
  · -- Component 2
    let Φ2 : ℝ × ℝ → ℂ := fun ζ =>
      ghat k ζ.1 ζ.2 0 * ((ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2) * σh ζ
    have hΦ2m : AEStronglyMeasurable Φ2 volume := by
      have hm : Measurable (fun ζ : ℝ × ℝ => (ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2) := by fun_prop
      exact (hghat_m.aestronglyMeasurable.mul hm.aestronglyMeasurable).mul hσm
    let B2 : ℝ × ℝ → ℝ := fun ζ => (1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖
    have hΦ2B : ∀ ζ, ‖Φ2 ζ‖ ≤ B2 ζ := by
      intro ζ
      simp only [Φ2, B2, norm_mul]
      have hsq : ‖(ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2‖ = ζ.1 ^ 2 + ζ.2 ^ 2 := by
        have : (ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2 = ((ζ.1 ^ 2 + ζ.2 ^ 2 : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      rw [hsq]
      nlinarith [norm_nonneg (ghat k ζ.1 ζ.2 0), norm_nonneg (σh ζ)]
    refine (htendsto_mode Φ2 hΦ2m B2 hσ hΦ2B).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hpt2 : (pt x y z) 2 = z := by simp [pt]
    have hmode : ∀ ζ : ℝ × ℝ, mode ζ.1 ζ.2 (pt x y z) = planeWave ζ.1 ζ.2 x y := fun ζ => by simp [mode, pt]
    simp only [mieE, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hcurl_curl_zhat, hcurl_zhat,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_zero, add_zero]
    rw [hpd2_u 0 0 (Or.inl rfl) (pt x y z) (by rw [hpt2]; exact hz),
        hpd2_u 1 1 (Or.inr rfl) (pt x y z) (by rw [hpt2]; exact hz)]
    simp only [hpt2, hmode]
    rw [← MeasureTheory.integral_add (hint_u00 z hz) (hint_u11 z hz), ← MeasureTheory.integral_neg]
    congr 1; ext ζ
    simp only [Φ2]
    ring_nf; simp [Complex.I_sq]
