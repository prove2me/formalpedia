-- Prove2me | Definitions.Def_QAlgorithms_Defs_GaussianSmoothing
-- name    : QAlgorithms_Defs_GaussianSmoothing
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:23:24.756138+00:00
-- url     : https://prove2.me/theorems/29b02f13-b8a8-43a8-a825-e26dd05ff5da
-- title:
--   GaussianSmoothing
-- statement:
--   GaussianSmoothing
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\GaussianSmoothing.lean

import Definitions.Def_QAlgorithms_Defs_ContinuousOraclePrograms
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QAlgorithms.StochasticOptimization

variable {d : ℕ}

/-- Centered Gaussian with covariance r^2 I, 2308.01582 p.12 Eq.(8).
The scalar radius is positive; the scaling map is measurable. -/
def smoothingGaussian (d : ℕ) (r : ℝ) (hr : 0 < r) : Measure (Vector d) :=
  (ProbabilityTheory.stdGaussian (Vector d)).map (fun y => r • y)

/-- The constructed smoothing distribution has unit mass
(2308.01582 p.12 Eq.(8)). -/
instance smoothingGaussian_probability (d : ℕ) (r : ℝ) (hr : 0 < r) :
    IsProbabilityMeasure (smoothingGaussian d r hr) := by
  unfold smoothingGaussian
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Gaussian convolution computed from f (2308.01582 p.12 Eq.(8)).
Integrability prevents the Bochner integral's junk zero value. -/
def gaussianSmoothing {d : ℕ} (f : Vector d → ℝ) (r : ℝ) (hr : 0 < r)
    (integrable : ∀ x, Integrable (fun y => f (x-y)) (smoothingGaussian d r hr))
    (x : Vector d) : ℝ :=
  ∫ y, f (x-y) ∂smoothingGaussian d r hr

/-- The smoothed gradient law is the Gaussian mixture of original query
laws, 2308.01582 pp.13–14 Eqs.(9)–(11). -/
def smoothedGradientLaw {d : ℕ} {f : Vector d → ℝ}
    (S : StochasticGradientLaw d f) (r : ℝ) (hr : 0 < r) (x : Vector d) : Measure (Vector d) :=
  (smoothingGaussian d r hr).bind (fun y => S.kernel (x-y))

/-- Exact public preparation and register swap for Eq.(11),
2308.01582 p.14. The preparation is a normalized clean Gaussian
superposition over shifted query points; its specification mentions no
unknown objective, gradient law, or oracle unitary. -/
structure GaussianQueryLayout (d : ℕ) (H W : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (R : GradientRegisters d H W) (r : ℝ) (hr : 0 < r) where
  outputRegisters : SamplingRegisters d H
  prepare : Vector d → H ≃ₗᵢ[ℂ] H
  prepared_clean : ∀ x, prepare x outputRegisters.zero ∈ R.cleanSpace
  prepared_query_law : ∀ x,
    R.queryMeasurement.born (prepare x outputRegisters.zero) =
      (smoothingGaussian d r hr).map (fun y => x-y)
  reorder : H ≃ₗᵢ[ℂ] H
  reorder_value_law : ∀ psi,
    outputRegisters.measurement.born (reorder psi) = R.valueMeasurement.born psi

/-- Constructed smoothed sampling oracle, 2308.01582 p.14 Eq.(11):
prepare the Gaussian shifted query, apply the original coherent QSGO,
and swap the value/garbage registers. The exact mixture law is derived
below; it is not an assumed performance field. -/
def smoothedGradientOracle {d : ℕ} {H W : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    {R : GradientRegisters d H W} {r : ℝ} {hr : 0 < r}
    (layout : GaussianQueryLayout d H W R r hr)
    {f : Vector d → ℝ} (O : QuantumStochasticGradientOracle d f H W R)
    (x : Vector d) : QuantumSamplingOracle d H layout.outputRegisters where
  distribution := smoothedGradientLaw O.stochastic r hr x
  probability := by
    letI := O.stochastic.markov
    unfold smoothedGradientLaw
    apply isProbabilityMeasure_bind
    · exact (O.stochastic.kernel.measurable.comp (by fun_prop)).aemeasurable
    · exact Filter.Eventually.of_forall (fun _ => inferInstance)
  unitary := ((layout.prepare x).trans O.unitary).trans layout.reorder
  law := by
    apply Measure.ext
    intro C hC
    change layout.outputRegisters.measurement.born
      (layout.reorder (O.unitary (layout.prepare x layout.outputRegisters.zero))) C =
        smoothedGradientLaw O.stochastic r hr x C
    rw [layout.reorder_value_law]
    have hn : ‖layout.prepare x layout.outputRegisters.zero‖ = 1 := by
      rw [LinearIsometryEquiv.norm_map, layout.outputRegisters.zero_norm]
    have h := O.joint_law (layout.prepare x layout.outputRegisters.zero)
      (layout.prepared_clean x) hn Set.univ C MeasurableSet.univ hC
    simp only [R.queryMeasurement.total, ContinuousLinearMap.id_apply, Measure.restrict_univ] at h
    rw [R.valueMeasurement.born_eq _ C hC, h, layout.prepared_query_law]
    rw [lintegral_map (O.stochastic.kernel.measurable_coe hC) (by fun_prop)]
    unfold smoothedGradientLaw
    exact (Measure.bind_apply (f := fun y : Vector d => O.stochastic.kernel (x-y)) hC
      (O.stochastic.kernel.measurable.comp (by fun_prop)).aemeasurable).symm

/-- Counted forward/inverse circuit word for the same smoothed oracle,
2308.01582 p.14. Each expansion contains one original query. -/
def smoothedQueryWord {d : ℕ} {H W : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    {R : GradientRegisters d H W} {r : ℝ} {hr : 0 < r}
    (layout : GaussianQueryLayout d H W R r hr) (x : Vector d)
    (inverse : Bool) (next : ContinuousOracleProgram d H) : ContinuousOracleProgram d H :=
  if inverse then .known layout.reorder.symm (.query true (.known (layout.prepare x).symm next))
  else .known (layout.prepare x) (.query false (.known layout.reorder next))

/-- Sanity check for the modeled source objects (arxiv-2308.01582v2, PDF pp.12,13,14). -/
example {H W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    {R : GradientRegisters d H W} {r : ℝ} {hr : 0 < r}
    (layout : GaussianQueryLayout d H W R r hr)
    {f : Vector d → ℝ} (O : QuantumStochasticGradientOracle d f H W R) (x : Vector d) :
    (smoothedGradientOracle layout O x).distribution = smoothedGradientLaw O.stochastic r hr x := rfl

end QAlgorithms.StochasticOptimization


