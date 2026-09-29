-- Prove2me | Definitions.Def_fep2_gaussian_vfe
-- name    : fep2_gaussian_vfe
-- status  : Definition
-- author  : @ActiveInference
-- created : 2026-09-24T17:20:32.324802+00:00
-- url     : https://prove2.me/theorems/8411843b-a856-4a3c-a707-b037e5c3cc11
-- title:
--   Scalar Gaussian filter and posterior-form Gaussian variational free energy
-- statement:
--   The Gaussian instantiation of the posterior-form variational free energy, self-contained on Mathlib's native real Gaussian laws.
--
--   A **fixed-variance Gaussian family** fixes one strictly positive variance $v$ and varies the location: each member is Mathlib's `gaussianReal` law $\mathcal{N}(\mu, v)$ with its canonical density $\mathsf{gaussianPDF}$. Its native KL is exact: for two locations $\mu_1,\mu_2$,
--   $$D_{\mathrm{KL}}\big(\mathcal{N}(\mu_1,v)\,\|\,\mathcal{N}(\mu_2,v)\big) = \frac{(\mu_1-\mu_2)^2}{2v},$$
--   proved against Mathlib's log-likelihood-ratio definition of KL with no finiteness hypotheses beyond the fixed positive variance.
--
--   A scalar **Ornstein–Uhlenbeck parameter block** (rate, center, diffusion variance rate) gives the one-step prediction: mean $c + e^{-\kappa\tau}(m - c)$ and variance $v\,e^{-2\kappa\tau} + \gamma\tau$-style closed forms that stay strictly positive. The **scalar Gaussian filter** then owns prediction, the fixed-noise Gaussian observation kernel, the closed gain, and the closed posterior mean and variance
--   $$m^* = m_p + K\,(o - m_p), \qquad v^* = \frac{v_p\,r}{v_p + r},$$
--   with innovation variance $v_p + r$ strictly positive — so every posterior remains a nondegenerate family member. The **evidence law** is the prediction-observation composition, with its candidate Gaussian density at the predicted mean.
--
--   The **posterior-form Gaussian variational free energy** at recognition mean $\mu$ is the native recognition-to-posterior KL
--   $$F[m] = D_{\mathrm{KL}}\big(\mathcal{N}(m,v^*)\,\|\,\mathcal{N}(m^*,v^*)\big) + S(o),$$
--   where the **evidence surprisal** $S(o) = -\log \rho(o)$ is taken against the candidate evidence density. The recognition family is the fixed-variance family over $m$; zero variances, multivariate laws, and manifold geometry stay outside this definition, and the natural-gradient layer is deliberately not included.
-- source:
--   fep_lean / fep_formal v1.2.0 (Active Inference Institute), FepSketches.gaussian_information_geometry.lean + FepSketches.scalar_gaussian_semigroup.lean + FepSketches.compositions.gaussian_filter.lean + FepSketches.compositions.smooth_reference_kernel.lean (all proved, 0 sorry); https://github.com/ActiveInferenceInstitute/fep_formal

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Tactic

/-!
# Gaussian variational free energy (mission substrate)

Mission `Free Energy Principle II` Gaussian substrate, transcribed from the
proved modules `FepSketches.gaussian_information_geometry`,
`FepSketches.scalar_gaussian_semigroup`, `FepSketches.compositions.gaussian_filter`,
and `FepSketches.compositions.smooth_reference_kernel` of the fep_lean
formalization (Active Inference Institute).  One nondegenerate scalar Gaussian
location family with fixed variance owns the native Mathlib law, and an exact
scalar Gaussian filter (OU prediction, Gaussian observation, closed update)
owns the posterior mean/variance the recognition family varies over.  The
posterior-form Gaussian variational free energy is the native
recognition-to-posterior KL plus the density-relative evidence surprisal; the
mission's theorems derive its mean-square-plus-surprisal form.
-/

namespace FreeEnergyPrinciple

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal MeasureTheory NNReal ProbabilityTheory

noncomputable section

/-! ## Fixed-variance scalar Gaussian location family -/

/-- A scalar Gaussian location family with one fixed, strictly positive
variance. The location remains an explicit argument of `law`; normalization,
density, support, and information identities are derived theorems. -/
structure FixedVarianceGaussian where
  variance : ℝ≥0
  variance_pos : 0 < variance

namespace FixedVarianceGaussian

/-- The native Mathlib density of the family member at `mean`. -/
noncomputable def density (family : FixedVarianceGaussian) (mean : ℝ) : ℝ → ℝ≥0∞ :=
  gaussianPDF mean family.variance

/-- The native probability law of the family member at `mean`. -/
noncomputable def law (family : FixedVarianceGaussian) (mean : ℝ) : Measure ℝ :=
  gaussianReal mean family.variance

/-- The family law is definitionally the pinned Mathlib real Gaussian. -/
theorem law_eq_gaussianReal (family : FixedVarianceGaussian) (mean : ℝ) :
    family.law mean = gaussianReal mean family.variance := rfl

/-- Every family member is volume weighted by its canonical density. -/
theorem law_eq_withDensity (family : FixedVarianceGaussian) (mean : ℝ) :
    family.law mean = volume.withDensity (family.density mean) := by
  exact gaussianReal_of_var_ne_zero mean family.variance_pos.ne'

/-- Equal positive variance makes every pair of family members mutually
absolutely continuous. -/
theorem law_mutuallyAbsolutelyContinuous
    (family : FixedVarianceGaussian) (sourceMean referenceMean : ℝ) :
    family.law sourceMean ≪ family.law referenceMean ∧
      family.law referenceMean ≪ family.law sourceMean := by
  constructor
  · exact
      (gaussianReal_absolutelyContinuous sourceMean family.variance_pos.ne').trans
        (gaussianReal_absolutelyContinuous' referenceMean family.variance_pos.ne')
  · exact
      (gaussianReal_absolutelyContinuous referenceMean family.variance_pos.ne').trans
        (gaussianReal_absolutelyContinuous' sourceMean family.variance_pos.ne')

private theorem densityReal_ratio
    (family : FixedVarianceGaussian) (sourceMean referenceMean x : ℝ) :
    gaussianPDFReal sourceMean family.variance x /
        gaussianPDFReal referenceMean family.variance x =
      Real.exp
        (((sourceMean - referenceMean) / (family.variance : ℝ)) * x +
          (referenceMean ^ 2 - sourceMean ^ 2) /
            (2 * (family.variance : ℝ))) := by
  rw [gaussianPDFReal_def, gaussianPDFReal_def]
  have hvarianceReal : 0 < (family.variance : ℝ) := by
    exact_mod_cast family.variance_pos
  have hnormalizer :
      (Real.sqrt (2 * Real.pi * (family.variance : ℝ)))⁻¹ ≠ 0 := by
    exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by positivity)))
  rw [mul_div_mul_left _ _ hnormalizer, ← Real.exp_sub]
  congr 1
  field_simp [family.variance_pos.ne']
  ring

private theorem law_llr
    (family : FixedVarianceGaussian) (sourceMean referenceMean : ℝ) :
    llr (family.law sourceMean) (family.law referenceMean) =ᵐ[family.law sourceMean]
      fun x =>
        ((sourceMean - referenceMean) / (family.variance : ℝ)) * x +
          (referenceMean ^ 2 - sourceMean ^ 2) /
            (2 * (family.variance : ℝ)) := by
  change
    llr (gaussianReal sourceMean family.variance)
        (gaussianReal referenceMean family.variance) =ᵐ[
          gaussianReal sourceMean family.variance]
      fun x =>
        ((sourceMean - referenceMean) / (family.variance : ℝ)) * x +
          (referenceMean ^ 2 - sourceMean ^ 2) /
            (2 * (family.variance : ℝ))
  have hsourceVolume : gaussianReal sourceMean family.variance ≪ volume := by
    exact gaussianReal_absolutelyContinuous sourceMean family.variance_pos.ne'
  have hreferenceVolume : gaussianReal referenceMean family.variance ≪ volume := by
    exact gaussianReal_absolutelyContinuous referenceMean family.variance_pos.ne'
  have hsourceReference :
      gaussianReal sourceMean family.variance ≪
        gaussianReal referenceMean family.variance := by
    simpa [law] using
      (family.law_mutuallyAbsolutelyContinuous sourceMean referenceMean).1
  filter_upwards
    [hsourceReference
      (Measure.rnDeriv_eq_div hsourceVolume hreferenceVolume),
    hsourceVolume (rnDeriv_gaussianReal sourceMean family.variance),
    hsourceVolume (rnDeriv_gaussianReal referenceMean family.variance)] with
      x hratio hsource hreference
  rw [llr, hratio, hsource, hreference, ENNReal.toReal_div,
    toReal_gaussianPDF, toReal_gaussianPDF,
    family.densityReal_ratio sourceMean referenceMean, Real.log_exp]

private theorem law_llr_integrable
    (family : FixedVarianceGaussian) (sourceMean referenceMean : ℝ) :
    Integrable
      (llr (family.law sourceMean) (family.law referenceMean))
      (family.law sourceMean) := by
  change
    Integrable
      (llr (gaussianReal sourceMean family.variance)
        (gaussianReal referenceMean family.variance))
      (gaussianReal sourceMean family.variance)
  have hllr :
      llr (gaussianReal sourceMean family.variance)
          (gaussianReal referenceMean family.variance) =ᵐ[
            gaussianReal sourceMean family.variance]
        fun x =>
          ((sourceMean - referenceMean) / (family.variance : ℝ)) * x +
            (referenceMean ^ 2 - sourceMean ^ 2) /
              (2 * (family.variance : ℝ)) := by
    simpa [law] using family.law_llr sourceMean referenceMean
  rw [integrable_congr hllr]
  have hid : Integrable id (gaussianReal sourceMean family.variance) := by
    exact
      (memLp_id_gaussianReal
        (μ := sourceMean) (v := family.variance) 1).integrable le_rfl
  exact
    (Integrable.const_mul hid
      ((sourceMean - referenceMean) / (family.variance : ℝ))).add
      (integrable_const
        ((referenceMean ^ 2 - sourceMean ^ 2) /
          (2 * (family.variance : ℝ))))

/-- Native KL from the source location to the reference location is the
extended-real embedding of their squared mean displacement divided by twice
the fixed variance. -/
theorem klDiv_law_eq_meanSquare
    (family : FixedVarianceGaussian) (sourceMean referenceMean : ℝ) :
    InformationTheory.klDiv
        (family.law sourceMean)
        (family.law referenceMean) =
      ENNReal.ofReal
        ((sourceMean - referenceMean) ^ 2 /
          (2 * (family.variance : ℝ))) := by
  change
    InformationTheory.klDiv
        (gaussianReal sourceMean family.variance)
        (gaussianReal referenceMean family.variance) =
      ENNReal.ofReal
        ((sourceMean - referenceMean) ^ 2 /
          (2 * (family.variance : ℝ)))
  have hac :
      gaussianReal sourceMean family.variance ≪
        gaussianReal referenceMean family.variance := by
    simpa [law] using
      (family.law_mutuallyAbsolutelyContinuous sourceMean referenceMean).1
  have hintegrable :
      Integrable
        (llr (gaussianReal sourceMean family.variance)
          (gaussianReal referenceMean family.variance))
        (gaussianReal sourceMean family.variance) := by
    simpa [law] using family.law_llr_integrable sourceMean referenceMean
  rw [InformationTheory.klDiv_of_ac_of_integrable hac hintegrable]
  congr 1
  have hllr :
      llr (gaussianReal sourceMean family.variance)
          (gaussianReal referenceMean family.variance) =ᵐ[
            gaussianReal sourceMean family.variance]
        fun x =>
          ((sourceMean - referenceMean) / (family.variance : ℝ)) * x +
            (referenceMean ^ 2 - sourceMean ^ 2) /
              (2 * (family.variance : ℝ)) := by
    simpa [law] using family.law_llr sourceMean referenceMean
  rw [integral_congr_ae hllr]
  have hid : Integrable id (gaussianReal sourceMean family.variance) := by
    exact
      (memLp_id_gaussianReal
        (μ := sourceMean) (v := family.variance) 1).integrable le_rfl
  have hscaled :
      Integrable
        (fun x =>
          ((sourceMean - referenceMean) / (family.variance : ℝ)) * x)
        (gaussianReal sourceMean family.variance) := by
    simpa only [id_eq] using
      Integrable.const_mul hid
        ((sourceMean - referenceMean) / (family.variance : ℝ))
  rw [integral_add hscaled
    (integrable_const
      ((referenceMean ^ 2 - sourceMean ^ 2) /
        (2 * (family.variance : ℝ)))), integral_const_mul]
  simp only [integral_id_gaussianReal]
  simp
  field_simp [family.variance_pos.ne']
  ring

end FixedVarianceGaussian

/-- Every member of a fixed-variance Gaussian family is a probability
measure. -/
instance fixedVarianceGaussian_law_isProbabilityMeasure
    (family : FixedVarianceGaussian) (mean : ℝ) :
    IsProbabilityMeasure (family.law mean) := by
  change IsProbabilityMeasure (gaussianReal mean family.variance)
  infer_instance

/-! ## Scalar OU prediction dynamics -/

/-- Raw parameters of the scalar mean-reverting transition. The diffusion
variance rate is the square of the diffusion-amplitude convention sometimes
written in scientific prose. -/
structure ScalarOUParameters where
  rate : ℝ
  rate_pos : 0 < rate
  center : ℝ
  diffusionVarianceRate : ℝ≥0
  diffusionVarianceRate_pos : 0 < diffusionVarianceRate

namespace ScalarOUParameters

/-- Exponential mean-reversion coefficient at nonnegative time. -/
noncomputable def decay (model : ScalarOUParameters) (time : ℝ≥0) : ℝ :=
  Real.exp (-model.rate * (time : ℝ))

private noncomputable def rateDenominator (model : ScalarOUParameters) : ℝ≥0 :=
  ⟨2 * model.rate, mul_nonneg (by norm_num) model.rate_pos.le⟩

/-- Variance of the invariant Gaussian law, derived from the raw variance
rate and mean-reversion rate. -/
noncomputable def stationaryVariance (model : ScalarOUParameters) : ℝ≥0 :=
  model.diffusionVarianceRate / model.rateDenominator

/-- Conditional transition mean from `state` at `time`. -/
noncomputable def transitionMean
    (model : ScalarOUParameters) (time : ℝ≥0) (state : ℝ) : ℝ :=
  model.center + model.decay time * (state - model.center)

private theorem decay_pos (model : ScalarOUParameters) (time : ℝ≥0) :
    0 < model.decay time := by
  exact Real.exp_pos _

private theorem decay_le_one (model : ScalarOUParameters) (time : ℝ≥0) :
    model.decay time ≤ 1 := by
  rw [decay, Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr model.rate_pos.le) time.2

private theorem stationaryVariance_pos (model : ScalarOUParameters) :
    0 < model.stationaryVariance := by
  exact div_pos model.diffusionVarianceRate_pos (by
    change 0 < model.rateDenominator
    exact_mod_cast mul_pos (by norm_num : (0 : ℝ) < 2) model.rate_pos)

/-- Conditional transition variance. -/
noncomputable def transitionVariance
    (model : ScalarOUParameters) (time : ℝ≥0) : ℝ≥0 :=
  ⟨(model.stationaryVariance : ℝ) * (1 - model.decay time ^ 2),
    mul_nonneg model.stationaryVariance.2
      (sub_nonneg.mpr (by
        nlinarith [model.decay_pos time, model.decay_le_one time]))⟩

end ScalarOUParameters

/-! ## Exact scalar Gaussian filtering -/

/-- A nondegenerate scalar Gaussian belief reusing the fixed-variance
family. -/
structure ScalarGaussianBelief where
  mean : ℝ
  family : FixedVarianceGaussian

namespace ScalarGaussianBelief

/-- The belief's native fixed-variance Gaussian law. -/
noncomputable def law (belief : ScalarGaussianBelief) : Measure ℝ :=
  belief.family.law belief.mean

noncomputable instance law_isProbabilityMeasure
    (belief : ScalarGaussianBelief) : IsProbabilityMeasure belief.law := by
  change IsProbabilityMeasure (gaussianReal belief.mean belief.family.variance)
  infer_instance

end ScalarGaussianBelief

/-- Raw inputs for one fixed-duration scalar prediction/update model. -/
structure ScalarGaussianFilterModel where
  dynamics : ScalarOUParameters
  stepDuration : ℝ≥0
  observationNoise : FixedVarianceGaussian

/-- Exact variance after evolving the prior through one OU step. -/
noncomputable def predictionVariance
    (model : ScalarGaussianFilterModel) (prior : ScalarGaussianBelief) : ℝ≥0 :=
  NNReal.mk (model.dynamics.decay model.stepDuration ^ 2) (sq_nonneg _) *
      prior.family.variance +
    model.dynamics.transitionVariance model.stepDuration

/-- A nondegenerate prior stays nondegenerate after every nonnegative OU
step. -/
theorem predictionVariance_pos
    (model : ScalarGaussianFilterModel) (prior : ScalarGaussianBelief) :
    0 < predictionVariance model prior := by
  have hDecay : 0 < model.dynamics.decay model.stepDuration := Real.exp_pos _
  have hCoefficient :
      0 < NNReal.mk (model.dynamics.decay model.stepDuration ^ 2) (sq_nonneg _) := by
    exact_mod_cast sq_pos_of_pos hDecay
  exact add_pos_of_pos_of_nonneg
    (mul_pos hCoefficient prior.family.variance_pos)
    (model.dynamics.transitionVariance model.stepDuration).2

/-- Exact predicted Gaussian belief, with no stored prediction certificate. -/
noncomputable def predictionBelief
    (model : ScalarGaussianFilterModel)
    (prior : ScalarGaussianBelief) : ScalarGaussianBelief where
  mean := model.dynamics.transitionMean model.stepDuration prior.mean
  family :=
    { variance := predictionVariance model prior
      variance_pos := predictionVariance_pos model prior }

/-- Fixed-variance Gaussian observation kernel with the model's observation
noise. -/
noncomputable def observationKernel
    (model : ScalarGaussianFilterModel) : Kernel ℝ ℝ where
  toFun state := model.observationNoise.law state
  measurable' := by
    change Measurable
      (Function.uncurry gaussianReal ∘
        fun state : ℝ => (state, model.observationNoise.variance))
    exact measurable_gaussianReal.comp
      (Measurable.prodMk measurable_id measurable_const)

/-- Every observation row is a probability measure. -/
noncomputable instance observationKernel_isMarkovKernel
    (model : ScalarGaussianFilterModel) :
    IsMarkovKernel (observationKernel model) :=
  ⟨fun state => by
    change IsProbabilityMeasure (gaussianReal state model.observationNoise.variance)
    infer_instance⟩

/-- Predictive variance of the scalar evidence law. -/
noncomputable def innovationVariance
    (model : ScalarGaussianFilterModel) (prior : ScalarGaussianBelief) : ℝ≥0 :=
  let predicted := predictionBelief model prior
  predicted.family.variance + model.observationNoise.variance

/-- Closed scalar Gaussian gain, derived only after prediction. -/
noncomputable def gain
    (model : ScalarGaussianFilterModel) (prior : ScalarGaussianBelief) : ℝ :=
  let predicted := predictionBelief model prior
  (predicted.family.variance : ℝ) / (innovationVariance model prior : ℝ)

/-- Closed posterior mean at one observation. -/
noncomputable def posteriorMean
    (model : ScalarGaussianFilterModel) (prior : ScalarGaussianBelief)
    (observation : ℝ) : ℝ :=
  let predicted := predictionBelief model prior
  predicted.mean + gain model prior * (observation - predicted.mean)

/-- Closed posterior variance. -/
noncomputable def posteriorVariance
    (model : ScalarGaussianFilterModel) (prior : ScalarGaussianBelief) : ℝ≥0 :=
  let predicted := predictionBelief model prior
  predicted.family.variance * model.observationNoise.variance /
    innovationVariance model prior

/-- The evidence and update denominators are strictly positive. -/
theorem innovationVariance_pos
    (model : ScalarGaussianFilterModel) (prior : ScalarGaussianBelief) :
    0 < innovationVariance model prior := by
  exact add_pos
    (predictionBelief model prior).family.variance_pos
    model.observationNoise.variance_pos

/-- The closed posterior remains a nondegenerate fixed-variance Gaussian. -/
theorem posteriorVariance_pos
    (model : ScalarGaussianFilterModel) (prior : ScalarGaussianBelief) :
    0 < posteriorVariance model prior := by
  exact div_pos
    (mul_pos (predictionBelief model prior).family.variance_pos
      model.observationNoise.variance_pos)
    (innovationVariance_pos model prior)

/-- Fixed-variance family carrying the derived posterior variance. -/
noncomputable def posteriorFamily
    (model : ScalarGaussianFilterModel)
    (prior : ScalarGaussianBelief) : FixedVarianceGaussian where
  variance := posteriorVariance model prior
  variance_pos := posteriorVariance_pos model prior

/-- Closed-form updated belief at one observation. -/
noncomputable def posteriorBelief
    (model : ScalarGaussianFilterModel) (prior : ScalarGaussianBelief)
    (observation : ℝ) : ScalarGaussianBelief where
  mean := posteriorMean model prior observation
  family := posteriorFamily model prior

/-- Fixed-variance family carrying the exact Gaussian evidence variance. -/
noncomputable def evidenceFamily
    (model : ScalarGaussianFilterModel)
    (prior : ScalarGaussianBelief) : FixedVarianceGaussian where
  variance := innovationVariance model prior
  variance_pos := innovationVariance_pos model prior

/-- Actual evidence law obtained by composing prediction and observation. -/
noncomputable def evidenceLaw
    (model : ScalarGaussianFilterModel) (prior : ScalarGaussianBelief) : Measure ℝ :=
  observationKernel model ∘ₘ (predictionBelief model prior).law

/-- Candidate Gaussian evidence density: the evidence family's density at the
predicted mean. -/
noncomputable def evidenceDensity
    (model : ScalarGaussianFilterModel) (prior : ScalarGaussianBelief) : ℝ → ℝ≥0∞ :=
  let predicted := predictionBelief model prior
  (evidenceFamily model prior).density predicted.mean

/-! ## Posterior-form Gaussian variational free energy -/

/-- Evidence surprisal relative to the candidate evidence law's Lebesgue
density. -/
noncomputable def evidenceSurprisal
    (model : ScalarGaussianFilterModel) (prior : ScalarGaussianBelief)
    (observation : ℝ) : ℝ :=
  -Real.log (evidenceDensity model prior observation).toReal

/-- Continuous variational free energy on fixed-posterior-variance
recognition laws.  Native KL is oriented recognition-to-posterior. -/
noncomputable def gaussianVariationalFreeEnergy
    (model : ScalarGaussianFilterModel) (prior : ScalarGaussianBelief)
    (observation recognitionMean : ℝ) : ℝ :=
  (klDiv
      ((posteriorFamily model prior).law recognitionMean)
      ((posteriorBelief model prior observation).law)).toReal +
    evidenceSurprisal model prior observation

end

end FreeEnergyPrinciple


