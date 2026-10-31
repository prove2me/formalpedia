-- Prove2me | Definitions.Def_OAIQ22Ab000
-- name    : OAIQ22Ab000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T09:01:48.519138+00:00
-- url     : https://prove2.me/theorems/1227a0fd-f049-4c9b-bc52-d4d9f593fda3
-- title:
--   Definitions bundle OAIQ22Ab000 of the split of OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 259 declarations of OpenAI's Lean: 197 definitions, 4 inductive types or structures, 4 instances and 54 theorems. The definitions and types are `OAI.AffineBernstein.BalancedNormalized`, `OAI.AffineBernstein.HasLowerSectionModulus`, `OAI.AffineBernstein.InAffineLimitFamily`, `OAI.AffineBernstein.IsModelShape`, `OAI.AffineBernstein.IsSupportedSplitModel`, `OAI.AffineBernstein.LocalDistanceConverges`, `OAI.AffineBernstein.SectionBalance`, `OAI.AffineBernstein.abpContactSet`, `OAI.AffineBernstein.adjointEquiv`, `OAI.AffineBernstein.affineAreaDensity`, `OAI.AffineBernstein.affineBaseMap`, `OAI.AffineBernstein.affineDefining`, `OAI.AffineBernstein.affineDetBarrier`, `OAI.AffineBernstein.affineDetPhase`, `OAI.AffineBernstein.affineEpigraphFiber`, `OAI.AffineBernstein.affineEpigraphLogMeasure`, `OAI.AffineBernstein.affineEpigraphPullback`, `OAI.AffineBernstein.affineFiberHeight`, `OAI.AffineBernstein.affineFiberHorizontal`, `OAI.AffineBernstein.affineGraphConormal`, `OAI.AffineBernstein.affineGraphPullback`, `OAI.AffineBernstein.affineImageCapArea`, `OAI.AffineBernstein.affineImageLinearCapArea`, `OAI.AffineBernstein.affineParametricVariationArea`, `OAI.AffineBernstein.ambientCoordinates`, `OAI.AffineBernstein.ambientOrthant`, `OAI.AffineBernstein.ambientSwap`, `OAI.AffineBernstein.basisHessian`, `OAI.AffineBernstein.bilinearOfMatrix`, `OAI.AffineBernstein.capQuadratic`, `OAI.AffineBernstein.capTiltedCovector`, `OAI.AffineBernstein.capTiltedForm`, `OAI.AffineBernstein.cleGraphPullback`, `OAI.AffineBernstein.cleMatrix`, `OAI.AffineBernstein.continuousDetRows`, `OAI.AffineBernstein.coordinateAffineVariationArea`, `OAI.AffineBernstein.coordinateProjection`, `OAI.AffineBernstein.dirDeriv`, `OAI.AffineBernstein.dualCutoff`, `OAI.AffineBernstein.dualDetBarrier` and 161 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `AffineBernstein_ABPMatrix`, `AffineBernstein_ActualBaseCurvature`, `AffineBernstein_ActualFlatInverse`, `AffineBernstein_ActualInverseMetric`, `AffineBernstein_ActualLogMeasure`, `AffineBernstein_ActualLogMeasureFurther`, `AffineBernstein_ActualTubeWeights`, `AffineBernstein_AffineFamily`, `AffineBernstein_AffineInvariantCap`, `AffineBernstein_AffineParametricStationarity`, `AffineBernstein_AffineStripArea`, `AffineBernstein_AffineSupport`, `AffineBernstein_AmbientStraightening`, `AffineBernstein_AngularCalculus`, `AffineBernstein_BaseWeightedIBP`, `AffineBernstein_BilinearNewton`, `AffineBernstein_CapChangeOfVariables`, `AffineBernstein_CapCoordinates`, `AffineBernstein_CapCovariance`, `AffineBernstein_CapInverseBound`, `AffineBernstein_CompactIntegration`, `AffineBernstein_ConstantDetCalculus`, `AffineBernstein_ConvexGradientBound`, `AffineBernstein_ConvexLocalLimits`, `AffineBernstein_ConvexSmoothMax`, `AffineBernstein_DetBarrierPhase`, `AffineBernstein_DeterminantVariation`, `AffineBernstein_DirectionalJacobi`, `AffineBernstein_DualDetBarrier`, `AffineBernstein_DualDetPhase`, `AffineBernstein_DualHeightCalculus`, `AffineBernstein_EntireAndDoubling`, `AffineBernstein_EuclideanChain`, `AffineBernstein_FiniteProjectiveCharts`, `AffineBernstein_FixedBasisCoordinates`, `AffineBernstein_FlatBlockCalculus`, `AffineBernstein_FlatEulerCore`, `AffineBernstein_FlatLogEuler`, `AffineBernstein_FlatProductCoordinates`, `AffineBernstein_FlatTubeArea`, `AffineBernstein_FlatTubeEuler`, `AffineBernstein_GaussCoordinates`, `AffineBernstein_GeneralCapCoordinates`, `AffineBernstein_GraphAreaCharts`, `AffineBernstein_GraphBallArea`, `AffineBernstein_GraphParametricArea`, `AffineBernstein_HessianVariation`, `AffineBernstein_InteriorLimits`, `AffineBernstein_JointAngularCalculus`, `AffineBernstein_JointTubeMetrics`, `AffineBernstein_LinearNormalizationCalculus`, `AffineBernstein_LogBarrierCalculus`, `AffineBernstein_LogDetGradientEnergy`, `AffineBernstein_LogTubeMeasure`, `AffineBernstein_MatrixConcavity`, `AffineBernstein_MatrixMetric`, `AffineBernstein_MaximalModelExclusion`, `AffineBernstein_ModelCentering`, `AffineBernstein_ModelCenteringFurther`, `AffineBernstein_ModelPositiveSigma`, `AffineBernstein_NewtonBasis`, `AffineBernstein_NewtonTensor`, `AffineBernstein_NormalizedCaps`, `AffineBernstein_NormalizedCellGeometry`, `AffineBernstein_NormalizedDet`, `AffineBernstein_NormalizedLogVariance`, `AffineBernstein_OrthantGeometry`, `AffineBernstein_OrthantHeight`, `AffineBernstein_ParametricAffineArea`, `AffineBernstein_ParametricChangeOfCoordinates`, `AffineBernstein_ParametricGraphJets`, `AffineBernstein_ParametricInverseMetric`, `AffineBernstein_ParametricSmoothness`, `AffineBernstein_ParametricTransport`, `AffineBernstein_ParametricVariationAlgebra`, `AffineBernstein_PiolaAlgebra`, `AffineBernstein_PiolaDifferential`, `AffineBernstein_PositiveMatrixTraceBound`, `AffineBernstein_ProductAmbientCoordinates`, `AffineBernstein_QuadraticAffineImage`, `AffineBernstein_RadialAdjugate`, `AffineBernstein_RegularFiberDomain`, `AffineBernstein_SigmaCapHelpers`, `AffineBernstein_SigmaNormalization`, `AffineBernstein_SmoothCapTest`, `AffineBernstein_SmoothPositivePart`, `AffineBernstein_SphereAlgebra`, `AffineBernstein_SphereIntegration`, `AffineBernstein_SphereIsometry`, `AffineBernstein_SupportCoordinates`, `AffineBernstein_SupportGeometry`, `AffineBernstein_SupportHomogeneity`, `AffineBernstein_SupportVariation`, `AffineBernstein_TangentShiftCalculus`, `AffineBernstein_TargetCapLIntegral`, `AffineBernstein_TensorFlux`, `AffineBernstein_ThinSlices`, `AffineBernstein_TiltedTrace`, `AffineBernstein_TriangularGraph`, `AffineBernstein_TubeCombination`, `AffineBernstein_TubeCompactIntegral`, `AffineBernstein_TubeDensityVariation`, `AffineBernstein_TubeFrame`, `AffineBernstein_TubeSecondForm`, `AffineBernstein_TubeWeightAlgebra`, `AffineBernstein_UniformActualCells`, `AffineBernstein_UniformLogCells`, `AffineBernstein_UniformSphericalCap`, `AffineBernstein_WeightedDivergence`.
--
--   **Imports.** It imports the published bundle `Def_AffineBernstein`.
--
--   **Imported by** (directly, in this split): the statements `OAI.AffineBernstein.affineEpigraph_angular_literal_drift`, `OAI.AffineBernstein.affineEpigraph_flat_chart_global_area_lintegral`, `OAI.AffineBernstein.affineEpigraph_flat_chart_global_inverseArea_lintegral`, `OAI.AffineBernstein.affineEpigraph_flat_graph_injective`, `OAI.AffineBernstein.affineEpigraph_flat_parametrization`, `OAI.AffineBernstein.affineEpigraph_flat_tube_positive`, `OAI.AffineBernstein.affineEpigraph_global_log_coordinate_identity`, `OAI.AffineBernstein.affineEpigraph_invariant_f_smooth`, `OAI.AffineBernstein.affineEpigraph_invariant_tube_positive`, `OAI.AffineBernstein.affineEpigraph_product_area_chart`, `OAI.AffineBernstein.affineEpigraph_product_fiber_area_bound`, `OAI.AffineBernstein.affineEpigraph_product_minors_bound`, `OAI.AffineBernstein.affineEpigraph_sigma_normalization`, `OAI.AffineBernstein.affineEpigraph_sphere_inverseArea_two_flat_lintegral`, `OAI.AffineBernstein.affineEpigraph_supportConormal_inward`, `OAI.AffineBernstein.affineEpigraph_tube_angular_pair_nonneg`, `OAI.AffineBernstein.affineEpigraph_tube_angular_smooth`, `OAI.AffineBernstein.affineEpigraph_whole_graph_area_bound`, `OAI.AffineBernstein.affineMaximal_det_upper_of_section_control`, `OAI.AffineBernstein.affineMaximal_flatSupport_local_stationary`, `OAI.AffineBernstein.affineMaximal_flat_tube_weak_euler`, `OAI.AffineBernstein.affineMaximal_global_d_identity`, `OAI.AffineBernstein.affineMaximal_invariant_tube_f_equation`, `OAI.AffineBernstein.affineMaximal_local_chart_stationary`, `OAI.AffineBernstein.affineMaximal_no_normalized_maximal_model`, `OAI.AffineBernstein.affineMaximal_no_polynomial_logMeasure`, `OAI.AffineBernstein.affineMaximal_round_tube_f_equation`, `OAI.AffineBernstein.affineMaximal_tube_energy`, `OAI.AffineBernstein.affineMaximal_uniform_target_cap_lintegral_bound`, `OAI.AffineBernstein.balanced_affineMaximal_constant_det`, `OAI.AffineBernstein.balanced_constant_hessian`, `OAI.AffineBernstein.balanced_global_directional_bddAbove`, `OAI.AffineBernstein.balanced_hessian_range_compact`, `OAI.AffineBernstein.complete_affineMaximal_model_transverse_pos`, `OAI.AffineBernstein.complete_affineMaximal_positive_cap_area`, `OAI.AffineBernstein.complete_affineMaximal_uniform_spherical_cap_bound`, `OAI.AffineBernstein.graph_chart_weighted_affineArea_lintegral`, `OAI.AffineBernstein.normalized_balanced_det_bounds`, `OAI.AffineBernstein.normalized_critical_density`, `OAI.AffineBernstein.normalized_harmonic_no_two_extremes`, `OAI.AffineBernstein.normalized_log_variance`, `OAI.AffineBernstein.normalized_model_positive_face_mass`, `OAI.AffineBernstein.normalized_model_positive_log_mass`, `OAI.AffineBernstein.normalized_model_uniform_actual_sigma` and `OAI.AffineBernstein.normalized_supersolution_high_set_small`; the proofs of `OAI.AffineBernstein.affineEpigraph_angular_literal_drift`, `OAI.AffineBernstein.affineEpigraph_flat_chart_global_area_lintegral`, `OAI.AffineBernstein.affineEpigraph_flat_chart_global_inverseArea_lintegral`, `OAI.AffineBernstein.affineEpigraph_flat_graph_injective`, `OAI.AffineBernstein.affineEpigraph_flat_parametrization`, `OAI.AffineBernstein.affineEpigraph_flat_tube_positive`, `OAI.AffineBernstein.affineEpigraph_global_log_coordinate_identity`, `OAI.AffineBernstein.affineEpigraph_invariant_f_smooth`, `OAI.AffineBernstein.affineEpigraph_invariant_tube_positive`, `OAI.AffineBernstein.affineEpigraph_product_area_chart`, `OAI.AffineBernstein.affineEpigraph_product_fiber_area_bound`, `OAI.AffineBernstein.affineEpigraph_product_minors_bound`, `OAI.AffineBernstein.affineEpigraph_sigma_normalization`, `OAI.AffineBernstein.affineEpigraph_sphere_inverseArea_two_flat_lintegral`, `OAI.AffineBernstein.affineEpigraph_supportConormal_inward`, `OAI.AffineBernstein.affineEpigraph_tube_angular_pair_nonneg`, `OAI.AffineBernstein.affineEpigraph_tube_angular_smooth`, `OAI.AffineBernstein.affineEpigraph_whole_graph_area_bound`, `OAI.AffineBernstein.affineMaximal_det_upper_of_section_control`, `OAI.AffineBernstein.affineMaximal_flatSupport_local_stationary`, `OAI.AffineBernstein.affineMaximal_flat_tube_weak_euler`, `OAI.AffineBernstein.affineMaximal_global_d_identity`, `OAI.AffineBernstein.affineMaximal_invariant_tube_f_equation`, `OAI.AffineBernstein.affineMaximal_local_chart_stationary`, `OAI.AffineBernstein.affineMaximal_no_normalized_maximal_model`, `OAI.AffineBernstein.affineMaximal_no_polynomial_logMeasure`, `OAI.AffineBernstein.affineMaximal_round_tube_f_equation`, `OAI.AffineBernstein.affineMaximal_tube_energy`, `OAI.AffineBernstein.affineMaximal_uniform_target_cap_lintegral_bound`, `OAI.AffineBernstein.affine_bernstein`, `OAI.AffineBernstein.balanced_affineMaximal_constant_det`, `OAI.AffineBernstein.balanced_constant_hessian`, `OAI.AffineBernstein.balanced_global_directional_bddAbove`, `OAI.AffineBernstein.balanced_hessian_range_compact`, `OAI.AffineBernstein.complete_affineMaximal_model_transverse_pos`, `OAI.AffineBernstein.complete_affineMaximal_positive_cap_area`, `OAI.AffineBernstein.complete_affineMaximal_uniform_spherical_cap_bound`, `OAI.AffineBernstein.graph_chart_weighted_affineArea_lintegral`, `OAI.AffineBernstein.normalized_balanced_det_bounds`, `OAI.AffineBernstein.normalized_critical_density`, `OAI.AffineBernstein.normalized_harmonic_no_two_extremes`, `OAI.AffineBernstein.normalized_log_variance`, `OAI.AffineBernstein.normalized_model_positive_face_mass`, `OAI.AffineBernstein.normalized_model_positive_log_mass`, `OAI.AffineBernstein.normalized_model_uniform_actual_sigma` and `OAI.AffineBernstein.normalized_supersolution_high_set_small`.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_AffineBernstein

section
-- module Solutions.OAIQ22_AB.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_PiolaAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant, as a continuous map multilinear in its rows. -/
def continuousDetRows : ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ :=
  ⟨Matrix.detRowAlternating.toMultilinearMap, by
    change Continuous (Matrix.det : Matrix ι ι ℝ → ℝ)
    fun_prop⟩

@[simp] theorem continuousDetRows_apply (A : Matrix ι ι ℝ) :
    continuousDetRows A = A.det := rfl

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_PiolaDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Rows of the derivative of a list of scalar functions, in fixed directions. -/
def jacobianRows (F : ι → E → ℝ) (e : ι → E) (x : E) : Matrix ι ι ℝ :=
  fun l m => fderiv ℝ (F l) x (e m)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_WeightedDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section WeightedDivergence

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

/-- A fixed-direction derivative, used only as notation for the actual Fréchet derivative. -/
def dirDeriv (v : E) (f : E → ℝ) : E → ℝ := fun x => fderiv ℝ f x v

end WeightedDivergence

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_CompactIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/-- The density of affine area in the original graph coordinates. -/
def affineAreaDensity {n : ℕ} (u : Space n → ℝ) (x : Space n) : ℝ :=
  Real.rpow (hessian u x).det (1 / ((n : ℝ) + 2))

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_DeterminantVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section RadialCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The support-plane height `ν(o-X)` in original graph coordinates. -/
def radialSupport (u : E → ℝ) (o : E) (c : ℝ) (x : E) : ℝ :=
  c - u x + fderiv ℝ u x (x - o)

end RadialCalculus

/-- Restriction of an arbitrary ambient affine function to the original graph. -/
def graphAffineFunction {n : ℕ} (u : Space n → ℝ) (a : Space n →L[ℝ] ℝ)
    (b d : ℝ) (x : Space n) : ℝ := a x + b * u x + d

/-- The actual coordinate functional through the Euclidean-space equivalence. -/
def coordinateProjection (n : ℕ) (i : Fin n) : Space n →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap

@[simp] theorem coordinateProjection_apply (n : ℕ) (i : Fin n) (x : Space n) :
    coordinateProjection n i x = x i := rfl

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_MatrixConcavity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

/-- The affine pullback uses the continuous map associated with the actual
matrix, so its determinant and nonsingularity have their usual meanings. -/
def affineBaseMap {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (d : Space n) (y : Space n) : Space n :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B y + d

@[simp] theorem euclideanCLM_coordinateVector {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) : Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B (coordinateVector n j) i = B i j := by
  change Matrix.mulVec B (Pi.single j 1) i = B i j
  simp

/-- Change of base variables, positive vertical scaling, and arbitrary affine
height correction. This includes the normalization of sections in rigidity. -/
def affineGraphPullback {n : ℕ} (u : Space n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (d : Space n) (a : Space n →L[ℝ] ℝ) (c e : ℝ) : Space n → ℝ :=
  graphAffineFunction (fun y => u (affineBaseMap B d y)) a c e

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_CapCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

def equivMatrix {n : ℕ} (B : Space n ≃L[ℝ] Space n) : Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis B.toLinearEquiv.toLinearMap

def cleGraphPullback {n : ℕ} (u : Space n → ℝ) (B : Space n ≃L[ℝ] Space n)
    (d : Space n) (a : Space n →L[ℝ] ℝ) (c e : ℝ) (x : Space n) : ℝ :=
  a x+c*u (B x+d)+e

/-- A shear does not change height and straightens an upward vector. -/
def verticalShear {n : ℕ} (p : Space n) : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ) :=
  ({ toFun := fun z => (z.1-z.2 • p,z.2)
     invFun := fun z => (z.1+z.2 • p,z.2)
     map_add' := by intro x y; ext <;> simp [add_smul]; abel
     map_smul' := by intro t x; ext <;> simp [smul_sub,smul_smul]
     left_inv := by intro z; ext <;> simp
     right_inv := by intro z; ext <;> simp } :
     (Space n × ℝ) ≃ₗ[ℝ] (Space n × ℝ)).toContinuousLinearEquiv

@[simp] lemma verticalShear_apply {n : ℕ} (p : Space n) (z : Space n × ℝ) :
    verticalShear p z = (z.1-z.2 • p,z.2) := rfl

lemma vertical_map {n : ℕ} (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ))
    {c : ℝ} (hc : M (0,1) = (0,c)) (z : ℝ) : M (0,z) = (0,c*z) := by
  have hp : ((0 : Space n),z) = z • ((0 : Space n),1) := by simp
  rw [hp,map_smul,hc]
  simp [mul_comm]

lemma triangular_fst {n : ℕ} (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ))
    {c : ℝ} (hc : M (0,1) = (0,c)) (x : Space n) (t : ℝ) :
    (M (x,t)).1 = (M (x,0)).1 := by
  have he : (x,t) = (x,0)+((0 : Space n),t) := by simp
  rw [he,map_add,vertical_map M hc]
  simp

lemma triangular_symm_vertical {n : ℕ} (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ))
    {c : ℝ} (hc : M (0,1) = (0,c)) (hcn : c ≠ 0) :
    M.symm (0,1) = (0,c⁻¹) := by
  apply M.injective
  rw [M.apply_symm_apply,vertical_map M hc,mul_inv_cancel₀ hcn]

/-- The induced invertible horizontal map of a triangular ambient affine map. -/
def triangularBaseEquiv {n : ℕ} (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ))
    {c : ℝ} (hc : M (0,1) = (0,c)) (hcn : c ≠ 0) : Space n ≃L[ℝ] Space n :=
  ({ toFun := fun x => (M (x,0)).1
     invFun := fun y => (M.symm (y,0)).1
     map_add' := by intro x y; simpa using congrArg Prod.fst (M.map_add (x,0) (y,0))
     map_smul' := by intro t x; simpa using congrArg Prod.fst (M.map_smul t (x,0))
     left_inv := by
       intro x
       have h := triangular_fst M.symm (triangular_symm_vertical M hc hcn)
         (M (x,0)).1 (M (x,0)).2
       simpa using h.symm
     right_inv := by
       intro y
       have h := triangular_fst M hc (M.symm (y,0)).1 (M.symm (y,0)).2
       simpa using h.symm } : Space n ≃ₗ[ℝ] Space n).toContinuousLinearEquiv

@[simp] lemma triangularBaseEquiv_apply {n : ℕ}
    (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) {c : ℝ}
    (hc : M (0,1) = (0,c)) (hcn : c ≠ 0) (x : Space n) :
    triangularBaseEquiv M hc hcn x = (M (x,0)).1 := rfl

@[simp] lemma triangularBaseEquiv_symm_apply {n : ℕ}
    (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) {c : ℝ}
    (hc : M (0,1) = (0,c)) (hcn : c ≠ 0) (x : Space n) :
    (triangularBaseEquiv M hc hcn).symm x = (M.symm (x,0)).1 := rfl

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_CapChangeOfVariables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

def graphAmbientBasis (n : ℕ) : Module.Basis (Fin n ⊕ Unit) ℝ (Space n × ℝ) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.prod (Module.Basis.singleton Unit ℝ)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SmoothPositivePart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology

def smoothPositiveSlope (ε t : ℝ) : ℝ := Real.smoothTransition ((t+ε)/(2*ε))

def smoothPositivePart (ε t : ℝ) : ℝ := ∫ s in (-ε)..t, smoothPositiveSlope ε s

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ConvexSmoothMax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology

/-- The exact quadratics used in the positive-cap comparison. -/
def capQuadratic {n : ℕ} (c : Space n) (b α : ℝ) (x : Space n) : ℝ :=
  b + α * ‖x-c‖^2

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TriangularGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/-- The manuscript's epigraph; the domain is not silently replaced by all of space. -/
def sourceEpigraph {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ) : Set (Space n × ℝ) :=
  {p | p.1 ∈ Ω ∧ u p.1 ≤ p.2}

def triangularLinearHeight {n : ℕ}
    (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) : Space n →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ (Space n) ℝ).comp
    (M.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ (Space n) ℝ))

@[simp] lemma triangularLinearHeight_apply {n : ℕ}
    (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (x : Space n) :
    triangularLinearHeight M x = (M (x,0)).2 := rfl

def triangularGraphFunction {n : ℕ} (u : Space n → ℝ)
    (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) {c : ℝ}
    (hc : M (0,1) = (0,c)) (hcn : c ≠ 0) (v : Space n × ℝ) : Space n → ℝ :=
  let B := (triangularBaseEquiv M hc hcn).symm
  let a := (triangularLinearHeight M).comp B.toContinuousLinearMap
  cleGraphPullback u B (-B v.1) a c (v.2-a v.1)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_CapCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section CapCovariance

/-- Affine area of the actual cap, in the original global graph chart.
The determinant exponent is the one proved for the literal parametric density. -/
def affineImageCapArea {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ) (b : ℝ) : ℝ :=
  Real.rpow |L.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2)) *
    ∫ x in {x | x ∈ Ω ∧ (L (x,u x)+v).2 < b}, affineAreaDensity u x

end CapCovariance

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_AngularCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Orthogonal tangential projection when `e` is a unit vector. -/
def tangentProjection (e v : E) : E := v - inner ℝ e v • e

/- The ambient extension of the spherical gradient of a degree-one support function. -/
def sphereGradient (H : E → ℝ) (e : E) : E := gradient H e - H e • e

/- The round covariant derivative, using tangential projection of the ambient derivative. -/
def roundDerivative (V : E → E) (e v : E) : E :=
  tangentProjection e (fderiv ℝ V e v)

/- The spherical Hessian evaluated on tangent vectors. -/
def sphereHessian (H : E → ℝ) (e v w : E) : ℝ :=
  inner ℝ (roundDerivative (sphereGradient H) e v) w

def sphereRadius (H : E → ℝ) (e v w : E) : ℝ :=
  sphereHessian H e v w + H e * inner ℝ v w

def roundTensorDerivative (A : E → E →L[ℝ] E →L[ℝ] ℝ) (e u v w : E) : ℝ :=
  fderiv ℝ (fun x => A x (tangentProjection x v) (tangentProjection x w)) e u

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_GraphAreaCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {n : ℕ}

/-- Reciprocal projective chart of the Gauss covector. In the chart where
coordinate `i` dominates the normal, its image lies in a fixed cube. -/
def reciprocalChart (i : Fin n) (p : Space n) : Space n :=
  WithLp.toLp 2 (fun j => if j=i then (p i)⁻¹ else p j / p i)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ConvexGradientBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section GraphProjection
variable {n : ℕ}

/-- Projection to the coordinate hyperplane omitting the i-th original
base coordinate, represented in its standard n coordinates. -/
def graphProjection (u : Space n → ℝ) (i : Fin n) (x : Space n) : Space n :=
  WithLp.toLp 2 (Function.update (fun j => x j) i (u x))

end GraphProjection

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SupportGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

section CompleteSphericalDependencies
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section SupportGeometry
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- The literal support value, not a freely chosen support coordinate. -/
def supportValue (K : Set E) (ℓ : E →L[ℝ] ℝ) : ℝ := sSup (ℓ '' K)

/- A supporting first-order inequality for an arbitrary differentiable convex function. -/
def supportJacobian (d : E →L[ℝ] ℝ) (H : E →L[ℝ] (E →L[ℝ] ℝ))
    (ℓ : E →L[ℝ] ℝ) : (E × ℝ) →L[ℝ] (ℝ × (E →L[ℝ] ℝ)) :=
  (d.comp (ContinuousLinearMap.fst ℝ E ℝ)).prod
    (H.comp (ContinuousLinearMap.fst ℝ E ℝ) -
      (ContinuousLinearMap.snd ℝ E ℝ).smulRight ℓ)

@[simp] theorem supportJacobian_apply (d : E →L[ℝ] ℝ)
    (H : E →L[ℝ] (E →L[ℝ] ℝ)) (ℓ : E →L[ℝ] ℝ) (v : E × ℝ) :
    supportJacobian d H ℓ v = (d v.1, H v.1 - v.2 • ℓ) := rfl

/- Positive curvature gives the missing transversality of the support equations. -/

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

/- Fiber derivatives of the actual defining function. -/
def fiberGradient (F : S × E → ℝ) (p : S × E) : E →L[ℝ] ℝ :=
  fderiv ℝ (fun y => F (p.1, y)) p.2

def supportEquations (F : S × E → ℝ)
    (q : (S × (E →L[ℝ] ℝ)) × (E × ℝ)) : ℝ × (E →L[ℝ] ℝ) :=
  (F (q.1.1, q.2.1), fiberGradient F (q.1.1, q.2.1) - q.2.2 • q.1.2)

end SupportGeometry

/- Coordinate entries coincide with the actual second Fréchet differential. -/
/- The standing positive-Hessian hypothesis implies genuine convexity on
 the original open convex domain; this is not an additional hypothesis. -/

end CompleteSphericalDependencies

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_AffineSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- A genuine affine slice of the original epigraph, in arbitrary transverse
coordinates. -/
def affineEpigraphFiber {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (x : Space n) (z : ℝ) (A : E →L[ℝ] Space n) (b : E →L[ℝ] ℝ) : Set E :=
  {y | x + A y ∈ Ω ∧ u (x + A y) ≤ z + b y}

/- A compact nonempty affine epigraph fiber has no vertical direction. -/

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

/- The literal inverse image of the original epigraph under affine coordinates. -/
def affineEpigraphPullback {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ)) : Set (S × E) :=
  {p | (a + L p).1 ∈ Ω ∧ u (a + L p).1 ≤ (a + L p).2}

def affineFiberHorizontal {n : ℕ} (L : (S × E) ≃L[ℝ] (Space n × ℝ)) : E →L[ℝ] Space n :=
  (ContinuousLinearMap.fst ℝ (Space n) ℝ).comp
    (L.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ S E))

def affineFiberHeight {n : ℕ} (L : (S × E) ≃L[ℝ] (Space n × ℝ)) : E →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ (Space n) ℝ).comp
    (L.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ S E))

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_GaussCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/- The one-homogeneous extension of the literal spherical support function. -/
def homogeneousSupport (K : Set E) (e : E) : ℝ :=
  supportValue K (InnerProductSpace.toDual ℝ E e)

/- The actual support point, reconstructed by the derivative of the support value. -/
def gaussPoint (K : Set E) (e : E) : E := gradient (homogeneousSupport K) e

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualBaseCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/- The genuine defining function for any affine coordinates of the graph. -/
def affineDefining {n : ℕ} (u : Space n → ℝ) (a : Space n × ℝ)
    (L : V ≃L[ℝ] (Space n × ℝ)) (p : V) : ℝ := u (a + L p).1 - (a + L p).2

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeSecondForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Euler and the angular gradient identity give the genuine tangent conormal. -/
def supportParam (Y : S × E → E) (q : S × E) : S × E := (q.1, Y q)

def supportConormal (H : S × E → ℝ) (x : S × E) : (S × E) →L[ℝ] ℝ :=
  (fderiv ℝ H x).comp ((ContinuousLinearMap.id ℝ S).prodMap (0 : E →L[ℝ] E)) -
    (InnerProductSpace.toDual ℝ E x.2).comp (ContinuousLinearMap.snd ℝ S E)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def tubeBaseMatrix (H : S × E → ℝ) (x : S × E) (bS : Module.Basis ι ℝ S) :
    Matrix ι ι ℝ := Matrix.of fun i j =>
  -fderiv ℝ (fderiv ℝ H) x (bS i,0) (bS j,0)

def tubeRadiusMatrix (H : S × E → ℝ) (x : S × E) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    Matrix κ κ ℝ := Matrix.of fun i j =>
  fderiv ℝ (fderiv ℝ H) x (0,bE (Sum.inl i)) (0,bE (Sum.inl j))

def tubeTangent (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    ι ⊕ κ → S × E := Sum.elim (fun i => (bS i,0)) (fun j => (0,bE (Sum.inl j)))

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeDensityVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section TubeDensityVariation
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def tubeAreaDensity (B : Matrix ι ι ℝ) (R : Matrix κ κ ℝ) (δ : ℝ) : ℝ :=
  Real.rpow B.det δ * Real.rpow R.det (1-δ)

/- Literal Jacobi first variation of the tube density, including empty
angular matrices. This is the integrand needed in source (tube-euler). -/

end TubeDensityVariation

open Matrix

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_FlatBlockCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def flatBlockHessian (f : E → ℝ) (v : ι → E) (x : E) : Matrix ι ι ℝ :=
  fun i j => dirDeriv (v i) (dirDeriv (v j) f) x

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_RadialAdjugate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def radialShear (e : ι ⊕ Unit → ℝ) : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ :=
  Matrix.fromBlocks 1 (Matrix.of fun i _ => e (Sum.inl i)) 0 1

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SupportHomogeneity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

def normalScale (c : ℝ) : S × E →L[ℝ] S × E :=
  (ContinuousLinearMap.id ℝ S).prodMap (c • ContinuousLinearMap.id ℝ E)

omit [CompleteSpace E] in
@[simp] lemma normalScale_apply (c : ℝ) (q : S × E) :
    normalScale c q = (q.1,c • q.2) := rfl

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NewtonBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section NewtonBasis
open scoped Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def orthogonalChange (b c : OrthonormalBasis ι ℝ E) : Matrix ι ι ℝ :=
  Matrix.of fun i j => inner ℝ (b i) (c j)

end NewtonBasis
open scoped Matrix
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def tubeFullRadiusMatrix (H : S × E → ℝ) (q : S × E) (b : OrthonormalBasis ι ℝ E) :
    Matrix ι ι ℝ := Matrix.of fun i j =>
  fderiv ℝ (fderiv ℝ H) q (0,b i) (0,b j)

def tubeAngularDensity (H : S × E → ℝ) (q : S × E) (b : OrthonormalBasis ι ℝ E) : ℝ :=
  (tubeFullRadiusMatrix H q b).adjugate.trace

def invariantTubeF (H : S × E → ℝ) (bS : Module.Basis ι ℝ S)
    (b : OrthonormalBasis (κ ⊕ Unit) ℝ E) (δ : ℝ) (q : S × E) : ℝ :=
  δ * (Real.log (tubeBaseMatrix H q bS).det + Real.log (inner ℝ q.2 q.2) -
     Real.log (tubeAngularDensity H q b)) - Real.log (H q)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeWeightAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/- Literal invariant tube measure coefficient with respect to `ds dω`. -/
def tubeMeasureCoefficient (n : ℕ) (h B Q : ℝ) : ℝ :=
  h ^ (-(n : ℝ)/2) * Real.sqrt (B*Q)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualTubeWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- The manuscript's invariant density `μ₀` on base times unit normals. -/
def tubeMeasureDensity (n : ℕ) (H : S × E → ℝ) (bS : Module.Basis ι ℝ S)
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) (q : S × E) : ℝ :=
  tubeMeasureCoefficient n (H q) (tubeBaseMatrix H q bS).det (tubeAngularDensity H q bE)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_FlatEulerCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

def flatTestContraction (A : ι → ι → E → ℝ) (e : ι → E) (η : E → ℝ) (x : E) : ℝ :=
  ∑ i, ∑ j, A i j x * dirDeriv (e i) (dirDeriv (e j) η) x

def flatDoubleDivergence (A : ι → ι → E → ℝ) (e : ι → E) (x : E) : ℝ :=
  ∑ j, ∑ i, dirDeriv (e j) (dirDeriv (e i) (A i j)) x

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_HessianVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E F : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def tubeAreaFirstVariation (B D : Matrix ι ι ℝ) (R T : Matrix κ κ ℝ) (δ : ℝ) : ℝ :=
  δ * Real.rpow B.det (δ-1) * Real.rpow R.det (1-δ) *
    (∑ i, ∑ j, B.adjugate j i * D i j) +
  (1-δ) * Real.rpow B.det δ * Real.rpow R.det (-δ) *
    (∑ i, ∑ j, R.adjugate j i * T i j)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_FlatTubeEuler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι κ : Type*}

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def flatBaseEulerWeight (B : E → Matrix ι ι ℝ) (R : E → Matrix κ κ ℝ) (δ : ℝ)
    (x : E) : ℝ := -δ * Real.rpow (B x).det (δ-1) * Real.rpow (R x).det (1-δ)

def flatAngularEulerWeight (B : E → Matrix ι ι ℝ) (R : E → Matrix κ κ ℝ) (δ : ℝ)
    (x : E) : ℝ := (1-δ) * Real.rpow (B x).det δ * Real.rpow (R x).det (-δ)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_FlatLogEuler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def flatLogAreaRatio (B : E → Matrix ι ι ℝ) (R : E → Matrix κ κ ℝ) (δ : ℝ) (x : E) : ℝ :=
  δ * (Real.log (B x).det - Real.log (R x).det)

def flatInverseTrace (A : Matrix ι ι ℝ) (v : ι → E) (f : E → ℝ) (x : E) : ℝ :=
  ∑ j, ∑ i, A⁻¹ i j * dirDeriv (v j) (dirDeriv (v i) f) x

def flatInversePair (A : Matrix ι ι ℝ) (v : ι → E) (f g : E → ℝ) (x : E) : ℝ :=
  ∑ j, ∑ i, A⁻¹ i j * dirDeriv (v j) f x * dirDeriv (v i) g x

/- Exact logarithmic form of the two-block Euler equation. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricVariationAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def variationConormal (D : Matrix ι ι ℝ) (g d : ι → ℝ) (t : ℝ) (k : ι) : ℝ :=
  ∑ l, (g l + t * d l) * (1 + t • D)⁻¹ l k

/- The second form for that conormal. H,B are the Hessians of u,beta;
C k is the Hessian of the kth horizontal displacement. -/
def variationSecondForm (H B D : Matrix ι ι ℝ) (g d : ι → ℝ)
    (C : ι → Matrix ι ι ℝ) (t : ℝ) : Matrix ι ι ℝ :=
  H + t • B - t • (Matrix.of fun i j => ∑ k, variationConormal D g d t k * C k i j)

def variationAreaDensity (H B D : Matrix ι ι ℝ) (g d : ι → ℝ)
    (C : ι → Matrix ι ι ℝ) (δ : ℝ) (t : ℝ) : ℝ :=
  Real.rpow (variationSecondForm H B D g d C t).det δ *
    Real.rpow |(1 + t • D).det| ((Fintype.card ι : ℝ) * δ)

@[simp] lemma variationConormal_zero (D : Matrix ι ι ℝ) (g d : ι → ℝ) (k : ι) :
    variationConormal D g d 0 k = g k := by
  simp [variationConormal, Matrix.one_apply]

@[simp] lemma variationSecondForm_zero (H B D : Matrix ι ι ℝ) (g d : ι → ℝ)
    (C : ι → Matrix ι ι ℝ) : variationSecondForm H B D g d C 0 = H := by
  simp [variationSecondForm]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NewtonTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- The penultimate Newton tensor, defined polynomially, not using an inverse. -/
def newtonTensor (A : Matrix ι ι ℝ) : Matrix ι ι ℝ := fun i j =>
  fderiv ℝ (fun B : ι → ι → ℝ => Matrix.adjugate (Matrix.of B) i j) (fun l m => A l m)
    (fun l m => (1 : Matrix ι ι ℝ) l m)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_BilinearNewton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open scoped Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def bilinearOfMatrix (b : OrthonormalBasis ι ℝ E) (A : Matrix ι ι ℝ) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ∑ i, ∑ j, A i j • (InnerProductSpace.toDual ℝ E (b i)).smulRight
    (InnerProductSpace.toDual ℝ E (b j))

def basisHessian (b : OrthonormalBasis ι ℝ E) (H : E → ℝ) (x : E) : Matrix ι ι ℝ :=
  fun i j => fderiv ℝ (fderiv ℝ H) x (b i) (b j)

def supportNewtonTensor (b : OrthonormalBasis ι ℝ E) (H : E → ℝ) (x : E) :
    E →L[ℝ] E →L[ℝ] ℝ := bilinearOfMatrix b (newtonTensor (basisHessian b H x))

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SphereIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open scoped Pointwise
open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- The action of a genuine orthogonal coordinate change on the unit sphere. -/
def sphereIsometry (A : E ≃ₗᵢ[ℝ] E) : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1 :=
  A.toHomeomorph.subtype (fun x => by simp only [Metric.mem_sphere, dist_zero_right]; exact A.norm_map x |>.symm ▸ Iff.rfl)

variable [FiniteDimensional ℝ E]

def rotationGenerator (u v : E) : E →L[ℝ] E :=
  (InnerProductSpace.toDual ℝ E u).smulRight v -
    (InnerProductSpace.toDual ℝ E v).smulRight u

def planeProjection (u v : E) : E →L[ℝ] E :=
  (InnerProductSpace.toDual ℝ E u).smulRight u +
    (InnerProductSpace.toDual ℝ E v).smulRight v

def planeRotationMap (u v : E) (t : ℝ) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E + (Real.cos t - 1) • planeProjection u v +
    Real.sin t • rotationGenerator u v

theorem planeRotationMap_apply (u v x : E) (t : ℝ) :
    planeRotationMap u v t x = x +
      ((Real.cos t - 1) * inner ℝ u x - Real.sin t * inner ℝ v x) • u +
      (Real.sin t * inner ℝ u x + (Real.cos t - 1) * inner ℝ v x) • v := by
  simp only [planeRotationMap, planeProjection, rotationGenerator, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    InnerProductSpace.toDual_apply_apply, sub_apply]
  module

theorem planeRotationMap_inner {u v : E} (hu : inner ℝ u u = 1)
    (hv : inner ℝ v v = 1) (huv : inner ℝ u v = 0) (t : ℝ) (x y : E) :
    inner ℝ (planeRotationMap u v t x) (planeRotationMap u v t y) = inner ℝ x y := by
  have hvu : inner ℝ v u = 0 := by rw [real_inner_comm, huv]
  simp only [planeRotationMap_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hu, hv, huv, hvu,
    mul_zero, mul_one, add_zero]
  rw [real_inner_comm x u, real_inner_comm x v]
  linear_combination (inner ℝ x u * inner ℝ u y + inner ℝ x v * inner ℝ v y) *
    (Real.sin_sq_add_cos_sq t)

/- A genuine orthogonal rotation; its formula is the usual two-plane rotation,
not an assumed measure-invariant flow. -/
def planeRotation {u v : E} (hu : inner ℝ u u = 1)
    (hv : inner ℝ v v = 1) (huv : inner ℝ u v = 0) (t : ℝ) : E ≃ₗᵢ[ℝ] E :=
  LinearIsometryEquiv.ofSurjective
    ((planeRotationMap u v t).toLinearMap.isometryOfInner (planeRotationMap_inner hu hv huv t))
    (LinearMap.surjective_of_injective
      ((planeRotationMap u v t).toLinearMap.isometryOfInner
        (planeRotationMap_inner hu hv huv t)).injective)

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SphereAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- Ambient expression for the round divergence of the restriction to the unit sphere. -/
def roundDivergence (b : OrthonormalBasis ι ℝ E) (W : E → E) (e : E) : ℝ :=
  ∑ i, inner ℝ (b i) (fderiv ℝ W e (b i - inner ℝ e (b i) • e))

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TensorFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι]

def tangentProjectionCLM (e : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (InnerProductSpace.toDual ℝ E e).smulRight e

def tensorFlux (b : OrthonormalBasis ι ℝ E)
    (T : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E) (q : E) : E :=
  ∑ i, T q (tangentProjection q (b i)) (tangentProjection q (G q)) • b i

variable [DecidableEq ι]

def roundHessianContraction (b : OrthonormalBasis ι ℝ E)
    (T : E → E →L[ℝ] E →L[ℝ] ℝ) (g : E → ℝ) (e : E) : ℝ :=
  ∑ i, T e (tangentProjection e (b i))
    (tangentProjection e (fderiv ℝ (gradient g) e (tangentProjection e (b i))) -
      inner ℝ e (gradient g e) • tangentProjection e (b i))

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_JointAngularCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/- Partial fiber gradient, represented through the derivative of the joint scalar. -/
def jointAngularGradient (g : S × E → ℝ) (q : S × E) : E :=
  (InnerProductSpace.toDual ℝ E).symm ((fderiv ℝ g q).comp (ContinuousLinearMap.inr ℝ S E))

def jointAngularHessianVec (g : S × E → ℝ) (q : S × E) (v : E) : E :=
  (InnerProductSpace.toDual ℝ E).symm
    ((fderiv ℝ (fderiv ℝ g) q (0,v)).comp (ContinuousLinearMap.inr ℝ S E))

def jointNewtonTensor (H : S × E → ℝ) (b : OrthonormalBasis ι ℝ E) (q : S × E) :
    E →L[ℝ] E →L[ℝ] ℝ := bilinearOfMatrix b (newtonTensor (tubeFullRadiusMatrix H q b))

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricGraphJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/- The actual first derivative of the horizontal component, in graph coordinates. -/
def horizontalJacobian {n : ℕ} (a : Fin n → Space n → ℝ) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => dirDeriv (coordinateVector n j) (a i) x

/- The graph's normal component of an arbitrary parametrized velocity. -/
def normalVariation {n : ℕ} (u β : Space n → ℝ) (a : Fin n → Space n → ℝ)
    (x : Space n) : ℝ := β x - ∑ k, dirDeriv (coordinateVector n k) u x * a k x

/- The vertical velocity reconstructed from its normal part and horizontal part. -/
def verticalVariation {n : ℕ} (u η : Space n → ℝ) (a : Fin n → Space n → ℝ)
    (x : Space n) : ℝ := η x + ∑ k, dirDeriv (coordinateVector n k) u x * a k x

/- Actual affine-area density of the variation, in its exact graph jets. -/
def graphVariationArea {n : ℕ} (u β : Space n → ℝ) (a : Fin n → Space n → ℝ)
    (x : Space n) (t : ℝ) : ℝ :=
  variationAreaDensity (hessian u x) (hessian β x) (horizontalJacobian a x)
    (fun k => dirDeriv (coordinateVector n k) u x)
    (fun k => dirDeriv (coordinateVector n k) β x)
    (fun k => hessian (a k) x) (1 / ((n : ℝ) + 2)) t

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricSmoothness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

def graphVariationJacobian {n : ℕ} (a : Fin n → Space n → ℝ) (p : ℝ × Space n) :
    Matrix (Fin n) (Fin n) ℝ := 1 + p.1 • horizontalJacobian a p.2

def graphVariationSecond {n : ℕ} (u β : Space n → ℝ) (a : Fin n → Space n → ℝ)
    (p : ℝ × Space n) : Matrix (Fin n) (Fin n) ℝ :=
  variationSecondForm (hessian u p.2) (hessian β p.2) (horizontalJacobian a p.2)
    (fun i => dirDeriv (coordinateVector n i) u p.2)
    (fun i => dirDeriv (coordinateVector n i) β p.2) (fun k => hessian (a k) p.2) p.1

def graphVariationRegular {n : ℕ} (Ω : Set (Space n)) (u β : Space n → ℝ)
    (a : Fin n → Space n → ℝ) : Set (ℝ × Space n) :=
  {p | p.2 ∈ Ω ∧ (graphVariationJacobian a p).det ≠ 0 ∧ (graphVariationSecond u β a p).det ≠ 0}

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_JointTubeMetrics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section JointTubeMetrics
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def tubeBasePair (H : S × E → ℝ) (b : Module.Basis ι ℝ S) (f g : S × E → ℝ)
    (q : S × E) : ℝ := H q*flatInversePair (tubeBaseMatrix H q b) (fun i => (b i,(0:E))) f g q

def tubeBaseTrace (H : S × E → ℝ) (b : Module.Basis ι ℝ S) (g : S × E → ℝ)
    (q : S × E) : ℝ := H q*flatInverseTrace (tubeBaseMatrix H q b) (fun i => (b i,(0:E))) g q

def tubeAngularPair (H : S × E → ℝ) (b : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (f g : S × E → ℝ) (q : S × E) : ℝ :=
  H q/tubeAngularDensity H q b * supportNewtonTensor b (fun y => H (q.1,y)) q.2
    (tangentProjection q.2 (gradient (fun y => f (q.1,y)) q.2))
    (tangentProjection q.2 (gradient (fun y => g (q.1,y)) q.2))

def tubeAngularTrace (H : S × E → ℝ) (b : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (g : S × E → ℝ) (q : S × E) : ℝ :=
  H q/tubeAngularDensity H q b * roundHessianContraction b
    (supportNewtonTensor b (fun y => H (q.1,y))) (fun y => g (q.1,y)) q.2

end JointTubeMetrics

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_MatrixMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def inverseMatrixPair (A : Matrix ι ι ℝ) (x y : ι → ℝ) : ℝ :=
  ∑ j, ∑ i, A⁻¹ i j*x j*y i

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeCompactIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {S E : Type*} [NormedAddCommGroup S]
  [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure S} [μ.IsAddHaarMeasure]

def tubeOpenSet (D : Set S) : Set (S × E) := D ×ˢ {e : E | e ≠ 0}

def tubeLift (q : S × sphere (0:E) 1) : S × E := (q.1,(q.2:E))

def tubeIntegral (μ : Measure S) (M : S × E → ℝ) (σ : S → ℝ) (g : S × E → ℝ) : ℝ :=
  ∫ q : S × sphere (0:E) 1, M (tubeLift q)*σ q.1*g (tubeLift q) ∂μ.prod volume.toSphere

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_BaseWeightedIBP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def flatCofactorTrace (f : E → ℝ) (v : ι → E) (g : E → ℝ) (x : E) : ℝ :=
  ∑ j, ∑ i, (flatBlockHessian f v x).adjugate i j * dirDeriv (v j) (dirDeriv (v i) g) x

def flatCofactorPair (f : E → ℝ) (v : ι → E) (g h : E → ℝ) (x : E) : ℝ :=
  ∑ j, ∑ i, (flatBlockHessian f v x).adjugate i j * dirDeriv (v j) g x * dirDeriv (v i) h x

def flatCofactorFlux (f : E → ℝ) (v : ι → E) (β g : E → ℝ) (j : ι) (x : E) : ℝ :=
  ∑ i, (flatBlockHessian f v x).adjugate i j * β x * dirDeriv (v i) g x

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricAffineArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- The augmented tangent frame, with its transverse column last. -/
def parametricFrame {n : ℕ} (X : Space n → E) (ξ : E) (x : Space n) :
    Fin n ⊕ Unit → E :=
  Sum.elim (fun i => fderiv ℝ X x (coordinateVector n i)) (fun _ => ξ)

/- The literal second form with a conormal frozen at the point in question. -/
def parametricSecondForm {n : ℕ} (X : Space n → E) (ν : E →L[ℝ] ℝ)
    (x : Space n) : Matrix (Fin n) (Fin n) ℝ := hessian (fun y => ν (X y)) x

/- Source (affine-area), using a fixed ambient volume basis. -/
def parametricAreaDensity {n : ℕ} (b : Module.Basis (Fin n ⊕ Unit) ℝ E)
    (X : Space n → E) (ν : E →L[ℝ] ℝ) (ξ : E) (x : Space n) : ℝ :=
  Real.rpow (parametricSecondForm X ν x).det (1 / ((n : ℝ) + 2)) *
    Real.rpow |b.det (parametricFrame X ξ x)| ((n : ℝ) / ((n : ℝ) + 2))

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_GraphParametricArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

def horizontalVelocity {n : ℕ} (a : Fin n → Space n → ℝ) (x : Space n) : Space n :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => a i x)

def graphParamVariation {n : ℕ} (u β : Space n → ℝ) (a : Fin n → Space n → ℝ)
    (t : ℝ) (x : Space n) : Space n × ℝ :=
  (x + t • horizontalVelocity a x, u x + t * β x)

def graphParamConormal {n : ℕ} (u β : Space n → ℝ) (a : Fin n → Space n → ℝ)
    (x : Space n) (t : ℝ) : (Space n × ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.snd ℝ (Space n) ℝ - ∑ k,
    variationConormal (horizontalJacobian a x)
      (fun k => dirDeriv (coordinateVector n k) u x)
      (fun k => dirDeriv (coordinateVector n k) β x) t k •
      ((coordinateProjection n k).comp (ContinuousLinearMap.fst ℝ (Space n) ℝ))

@[simp] lemma graphParamConormal_apply {n : ℕ} (u β : Space n → ℝ)
    (a : Fin n → Space n → ℝ) (x : Space n) (t : ℝ) (z : Space n × ℝ) :
    graphParamConormal u β a x t z = z.2 - ∑ k,
      variationConormal (horizontalJacobian a x)
        (fun k => dirDeriv (coordinateVector n k) u x)
        (fun k => dirDeriv (coordinateVector n k) β x) t k * z.1 k := by
  simp [graphParamConormal]

@[simp] lemma graphParamConormal_vertical {n : ℕ} (u β : Space n → ℝ)
    (a : Fin n → Space n → ℝ) (x : Space n) (t : ℝ) :
    graphParamConormal u β a x t ((0 : Space n), 1) = 1 := by simp

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_AffineParametricStationarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/- The literal arbitrary affine image of a parametrized graph variation. -/
def affineParametricVariationArea {n : ℕ} (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ))
    (v : Space n × ℝ) (u β : Space n → ℝ) (a : Fin n → Space n → ℝ)
    (x : Space n) (t : ℝ) : ℝ :=
  parametricAreaDensity (graphAmbientBasis n)
    (fun y => L (graphParamVariation u β a t y) + v)
    ((graphParamConormal u β a x t).comp L.symm.toContinuousLinearMap)
    (L ((0 : Space n), 1)) x

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricChangeOfCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

def parametricJacobian {n : ℕ} (φ : Space n → Space n) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => fderiv ℝ φ x (coordinateVector n j) i

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

def coordinateAffineVariationArea {n : ℕ} (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ))
    (v : Space n × ℝ) (φ : Space n → Space n) (u β : Space n → ℝ)
    (a : Fin n → Space n → ℝ) (x : Space n) (t : ℝ) : ℝ :=
  parametricAreaDensity (graphAmbientBasis n)
    ((fun y => L (graphParamVariation u β a t y) + v) ∘ φ)
    ((graphParamConormal u β a (φ x) t).comp L.symm.toContinuousLinearMap)
    (L ((0 : Space n),1)) x

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SupportVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E F : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/- Homogeneous extension of an actual test function off the affine normal chart. -/
def flatNormalProjection (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) (q : S × E) : F :=
  C ((q.1, (ℓ q.2)⁻¹ • q.2)-q₀)

def flatSupportVariation (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) (η : F → ℝ) (q : S × E) : ℝ :=
  ℓ q.2 * η (flatNormalProjection ℓ q₀ C q)

def supportGradient (H : S × E → ℝ) (q : S × E) : E :=
  (InnerProductSpace.toDual ℝ E).symm (fiberGradient H q)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_FlatTubeArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- In a flat normal chart the final normal coordinate is one, and the
transverse column is the fixed negative final basis vector. -/
def flatTubeFrame (Y : S × E → E) (x : S × E) (bS : Module.Basis ι ℝ S)
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) : ι ⊕ (κ ⊕ Unit) → S × E :=
  Sum.elim (fun i => fderiv ℝ (supportParam Y) x (bS i,0))
    (Sum.elim (fun j => fderiv ℝ (supportParam Y) x (0,bE (Sum.inl j)))
      (fun _ => (0,-bE (Sum.inr ()))))

def flatTubeAffineAreaJet (H : S × E → ℝ) (Y : S × E → E) (x : S × E)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) : ℝ :=
  let n : ℝ := Fintype.card ι+Fintype.card κ
  Real.rpow (Matrix.of fun i j : ι ⊕ κ => supportConormal H x
      (fderiv ℝ (fderiv ℝ (supportParam Y)) x (tubeTangent bS bE i) (tubeTangent bS bE j))).det
        (1/(n+2)) *
    Real.rpow |(bS.prod bE.toBasis).det (flatTubeFrame Y x bS bE)| (n/(n+2))

/- Literal flat-normal-chart area density. No sphere measure change is
required to obtain the local variational equation in these coordinates. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeCombination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

def positiveOrthant (k : ℕ) : Set (Space k) := {s | ∀ i, 0 < s i}

def logSpace {k : ℕ} (s : Space k) : Space k :=
  (EuclideanSpace.equiv (Fin k) ℝ).symm (fun i => Real.log (s i))

def expSpace {k : ℕ} (s : Space k) : Space k :=
  (EuclideanSpace.equiv (Fin k) ℝ).symm (fun i => Real.exp (s i))

@[simp] lemma logSpace_apply {k : ℕ} (s : Space k) (i : Fin k) : logSpace s i = Real.log (s i) := rfl
@[simp] lemma expSpace_apply {k : ℕ} (s : Space k) (i : Fin k) : expSpace s i = Real.exp (s i) := rfl

@[simp] lemma logSpace_expSpace {k : ℕ} (s : Space k) : logSpace (expSpace s) = s := by
  ext i
  simp

def logPullback {k : ℕ} (φ : Space k → ℝ) (s : Space k) : ℝ :=
  @ite ℝ (s ∈ positiveOrthant k) (Classical.propDecidable _) (φ (logSpace s)) 0

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_EuclideanChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

def euclideanGradientSquare {k : ℕ} (φ : Space k → ℝ) (s : Space k) : ℝ :=
  ∑ i : Fin k, (fderiv ℝ φ s ((EuclideanSpace.basisFun (Fin k) ℝ) i))^2

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_LogTubeMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {k : ℕ} {μ : Measure (Space k)}

def logTubeMeasure (μ : Measure (Space k)) (D : Set (Space k)) (F : Space k × E → ℝ) :
    Measure (Space k) :=
  Measure.map (fun q : Space k × sphere (0:E) 1 => logSpace q.1)
    (((μ.prod (volume.toSphere : Measure (sphere (0:E) 1))).restrict
      (D ×ˢ Set.univ)).withDensity (fun q => ENNReal.ofReal (F (tubeLift q))))

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualLogMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

def tubeLogMassWeight {k : ℕ} (H : Space k × E → ℝ) (q : Space k × E) : ℝ :=
  1+∑ i : Fin k, tubeBasePair H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    (fun z => Real.log (z.1 i)) (fun z => Real.log (z.1 i)) q

/- Joint regularity and positivity of the actual source logarithmic density. -/
def affineEpigraphLogMeasure {n k : ℕ} (μ : Measure (Space k)) (D : Set (Space k))
    (Ω : Set (Space n)) (u : Space n → ℝ) (a : Space n × ℝ)
    (L : (Space k × E) ≃L[ℝ] (Space n × ℝ)) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    Measure (Space k) :=
  let H := fun q : Space k × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  logTubeMeasure μ D (fun q => tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE q *
    tubeLogMassWeight H q)

/- Actual measure form of Proposition log-inequality, with the Euclidean
operator norm of the true derivative in logarithmic coordinates. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ConvexLocalLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open scoped Topology NNReal

open Filter Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/- The local distance-function topology used in geometry.tex:70–101. Sets
are separately required to be nonempty and closed when those properties enter. -/
def LocalDistanceConverges (Cj : ℕ → Set E) (C : Set E) : Prop :=
  TendstoLocallyUniformly (fun j x => infDist x (Cj j)) (fun x => infDist x C) atTop

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_InteriorLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter Metric
open scoped Topology Pointwise

/- The geometric conditions of a k-model, in its distinguished coordinates.
Membership in the affine local-limit family is separate from these conditions. -/
structure IsModelShape {k m : ℕ} (C : Set (Space k × Space m)) : Prop where
  closed : IsClosed C
  convex : Convex ℝ C
  interior_nonempty : (interior C).Nonempty
  orthant : ∀ s : Space k, (∀ i, 0 ≤ s i) → (s, 0) ∈ C
  support : ∀ p ∈ C, ∀ i, 0 ≤ p.1 i
  compact_cap : ∀ T : ℝ, 0 ≤ T → IsCompact (C ∩ {p | ∑ i, p.1 i ≤ T})

/- The transverse fiber, including lower-dimensional and boundary fibers. -/
def modelFiber {k m : ℕ} (C : Set (Space k × Space m)) (s : Space k) : Set (Space m) :=
  {y | (s, y) ∈ C}

/- The ray containment recession argument in geometry.tex does not need
full-dimensionality. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SupportCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open Filter Metric
open scoped Topology Pointwise
open scoped Pointwise
open scoped Pointwise

section SupportCoordinates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- A nonzero real functional has full range. -/

variable [FiniteDimensional ℝ E]

/- The literal split along a normalized support vector. The second component
is the kernel of the support; no quotient or degenerate coordinate is used. -/
def splitFunctionalEquiv (ell : E →L[ℝ] ℝ) (w : E) (hw : ell w = 1) :
    E ≃L[ℝ] ℝ × ell.ker :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := fun x => (ell x, ⟨x - (ell x) • w, by simp [hw]⟩)
    invFun := fun p => p.1 • w + p.2
    left_inv := by intro x; simp
    right_inv := by
      rintro ⟨r, z⟩
      have hz : ell z = 0 := z.property
      ext
      · simp [hw, hz]
      · simp [hw, hz]
    map_add' := by
      intro x y
      ext
      · simp
      · simp [add_smul]; abel
    map_smul' := by
      intro a x
      ext
      · simp
      · simp [smul_sub, smul_smul] }

@[simp] theorem splitFunctionalEquiv_fst (ell : E →L[ℝ] ℝ) (w : E) (hw : ell w = 1) (x : E) :
    (splitFunctionalEquiv ell w hw x).1 = ell x := rfl

@[simp] theorem splitFunctionalEquiv_w (ell : E →L[ℝ] ℝ) (w : E) (hw : ell w = 1) :
    splitFunctionalEquiv ell w hw w = (1, 0) := by
  ext <;> simp [splitFunctionalEquiv, hw]

/- Coordinates which keep the support as the first coordinate and send a
chosen interior point of a convex fiber to (1,0). Scaling the support, rather
than translating the body, preserves the ambient origin and all recession rays. -/

end SupportCoordinates

/- Append one real base coordinate, placing it first in Fin (k+1). -/
def extendBaseEquiv (k : ℕ) : (Space k × ℝ) ≃L[ℝ] Space (k+1) :=
  (((ContinuousLinearEquiv.prodComm ℝ (Space k) ℝ).trans
      ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (EuclideanSpace.equiv (Fin k) ℝ))).trans
      (Fin.consLinearEquiv ℝ (fun _ : Fin (k+1) => ℝ)).toContinuousLinearEquiv).trans
    (EuclideanSpace.equiv (Fin (k+1)) ℝ).symm

def reorderThinEquiv (k d : ℕ) : (Space k × (ℝ × Space d)) ≃L[ℝ] (Space (k+1) × Space d) :=
  (ContinuousLinearEquiv.prodAssoc ℝ (Space k) ℝ (Space d)).symm.trans
    ((extendBaseEquiv k).prodCongr (ContinuousLinearEquiv.refl ℝ (Space d)))

@[simp] theorem reorderThin_zero {k d : ℕ} (p : Space k × (ℝ × Space d)) :
    (reorderThinEquiv k d p).1 0 = p.2.1 := rfl

@[simp] theorem reorderThin_succ {k d : ℕ} (p : Space k × (ℝ × Space d)) (i : Fin k) :
    (reorderThinEquiv k d p).1 i.succ = p.1 i := rfl

@[simp] theorem reorderThin_snd {k d : ℕ} (p : Space k × (ℝ × Space d)) :
    (reorderThinEquiv k d p).2 = p.2.2 := rfl

@[simp] theorem reorderThin_sum {k d : ℕ} (p : Space k × (ℝ × Space d)) :
    (∑ i : Fin (k+1), (reorderThinEquiv k d p).1 i) = (∑ i : Fin k, p.1 i) + p.2.1 := by
  rw [Fin.sum_univ_succ]
  simp [add_comm]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_AffineFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter Metric
open scoped Topology Pointwise

section AffineFamily
open Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/- For distance functions, pointwise convergence is automatically locally
uniform, by the common unit Lipschitz constant and a finite compact cover. -/
structure InAffineLimitFamily {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : Set E) (C : Set F) : Prop where
  closed : IsClosed C
  convex : Convex ℝ C
  interior_nonempty : (interior C).Nonempty
  approximation : ∃ A : ℕ → (E ≃ᴬ[ℝ] F), LocalDistanceConverges (fun j => A j '' D) C

end AffineFamily

open scoped Pointwise

/- The coordinate action of the actual matrix linear equivalence. -/

open scoped Pointwise

/- Exact centered normalization in geometry.tex (2/(C+1), 2n), proved
without importing John's theorem: first normalize the symmetric difference
body, then use the actual balance inclusion. -/

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ThinSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open Filter Metric
open scoped Topology Pointwise
open scoped Pointwise
open scoped Pointwise

open Filter Metric
open scoped Topology Pointwise
variable {k d : ℕ}

/- Thin slices and rescalings before reordering the k+1 base coordinates. -/
def thinSlice (C : Set (Space k × (ℝ × Space d))) (ε : ℝ) : Set (Space d) :=
  {z | (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ)), (ε, z)) ∈ C}

def thinRescaling (C : Set (Space k × (ℝ × Space d))) (ε : ℝ)
    (A : Space d ≃L[ℝ] Space d) : Set (Space k × (ℝ × Space d)) :=
  {p | (p.1, (ε * p.2.1, A.symm p.2.2)) ∈ C}

/- Supports and the original orthant after a support-coordinate split. -/
structure IsSupportedSplitModel (C : Set (Space k × (ℝ × Space d))) : Prop where
  closed : IsClosed C
  convex : Convex ℝ C
  orthant : ∀ s : Space k, (∀ i, 0 ≤ s i) → (s, (0, 0)) ∈ C
  base_support : ∀ p ∈ C, ∀ i, 0 ≤ p.1 i
  new_support : ∀ p ∈ C, 0 ≤ p.2.1
  compact_cap : ∀ T : ℝ, 0 ≤ T → IsCompact (C ∩ {p | ∑ i, p.1 i ≤ T})
  interior_one : (1, (0 : Space d)) ∈ interior
    {y | (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ)), y) ∈ C}

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ModelCentering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter Metric
open scoped Topology Pointwise
open scoped Pointwise
open scoped Pointwise

open Filter Metric
open scoped Topology Pointwise

variable {k m d : ℕ}

/- Transverse coordinate changes preserve the literal model conditions. -/

@[simp] theorem fiber_transverse_image {C : Set (Space k × Space m)}
    (A : Space m ≃L[ℝ] Space m) (s : Space k) :
    modelFiber (((ContinuousLinearEquiv.refl ℝ (Space k)).prodCongr A) '' C) s =
      A '' modelFiber C s := by
  ext y
  constructor
  · rintro ⟨p, hp, he⟩
    have hs : p.1 = s := congrArg Prod.fst he
    have hy : A p.2 = y := congrArg Prod.snd he
    exact ⟨p.2, by simpa only [modelFiber, mem_ofPred_eq, ← hs, Prod.mk.eta] using hp, hy⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(s,z), hz, rfl⟩

/- The actual support-coordinate change gives precisely the split model to
which the thin-slice construction applies. -/
def thinRescalingEquiv (k d : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (A : Space d ≃L[ℝ] Space d) :
    (Space k × (ℝ × Space d)) ≃L[ℝ] (Space k × (ℝ × Space d)) :=
  (ContinuousLinearEquiv.refl ℝ (Space k)).prodCongr
    (((LinearEquiv.smulOfNeZero ℝ ℝ ε hε).symm.toContinuousLinearEquiv).prodCongr A)

def positiveBaseEquiv (s : Space k) (hs : ∀ i, 0 < s i) : Space k ≃L[ℝ] Space k :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := fun x => WithLp.toLp 2 (fun i => x i / s i)
    invFun := fun x => WithLp.toLp 2 (fun i => s i * x i)
    left_inv := by intro x; ext i; exact mul_div_cancel₀ _ (hs i).ne'
    right_inv := by intro x; ext i; exact mul_div_cancel_left₀ _ (hs i).ne'
    map_add' := by intro x y; ext i; exact add_div _ _ _
    map_smul' := by intro a x; ext i; exact mul_div_assoc _ _ _ }

@[simp] theorem positiveBaseEquiv_apply (s : Space k) (hs : ∀ i, 0 < s i) (x : Space k) (i : Fin k) :
    positiveBaseEquiv s hs x i = x i / s i := rfl

@[simp] theorem positiveBaseEquiv_symm_apply (s : Space k) (hs : ∀ i, 0 < s i) (x : Space k) (i : Fin k) :
    (positiveBaseEquiv s hs).symm x i = s i * x i := rfl

@[simp] theorem positiveBaseEquiv_self (s : Space k) (hs : ∀ i, 0 < s i) :
    positiveBaseEquiv s hs s = WithLp.toLp 2 (fun _ : Fin k => (1:ℝ)) := by
  ext i
  exact div_self (hs i).ne'

/- Positive diagonal choices of the distinguished directions preserve all
model properties, in particular compactness of caps. -/

@[simp] theorem fiber_positive_base_image {C : Set (Space k × Space m)}
    (s : Space k) (hs : ∀ i, 0 < s i) :
    modelFiber (((positiveBaseEquiv s hs).prodCongr (ContinuousLinearEquiv.refl ℝ (Space m))) '' C)
      (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) = modelFiber C s := by
  ext y
  constructor
  · rintro ⟨p,hp,he⟩
    have he1 : positiveBaseEquiv s hs p.1 = positiveBaseEquiv s hs s := by
      simpa using congrArg Prod.fst he
    have he2 : p.2 = y := congrArg Prod.snd he
    have hp1 := (positiveBaseEquiv s hs).injective he1
    simpa only [modelFiber, mem_ofPred_eq, ← hp1, ← he2, Prod.mk.eta] using hp
  · intro hy
    exact ⟨(s,y),hy, by simp⟩

/- Geometry.tex Proposition 2.7: the centering constant is uniform over all
models, positive fibers, and admissible distinguished coordinates of a maximal
family. Zero-dimensional transverse fibers are included. -/

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NormalizedCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open Filter Metric
open scoped Topology Pointwise
open scoped Pointwise
open scoped Pointwise

open Filter Metric
open scoped Topology Pointwise

/- Quantitative cap transfer: a given limit radius costs only one unit.
The constant does not depend on the sequence or its limit set. -/
def positiveBaseForm {k m : ℕ} (a : Fin k → ℝ) : (Space k × Space m) →L[ℝ] ℝ :=
  (∑ i, a i • EuclideanSpace.proj i).comp (ContinuousLinearMap.fst ℝ (Space k) (Space m))

@[simp] lemma positiveBaseForm_apply {k m : ℕ} (a : Fin k → ℝ) (p : Space k × Space m) :
    positiveBaseForm a p = ∑ i, a i * p.1 i := by
  simp [positiveBaseForm,PiLp.proj_apply]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_RegularFiberDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section RegularFiberDomain
open Metric Filter

/-- The largest open positive base domain on which the literal transverse
fibers are compact and contain zero in their interiors. It is defined directly
from the convex body's fibers, without any estimate or derivative hypothesis. -/
def regularPositiveFiberDomain {k m : ℕ} (C : Set (Space k × Space m)) : Set (Space k) :=
  {s | ∃ U : Set (Space k), IsOpen U ∧ U ⊆ positiveOrthant k ∧ s ∈ U ∧
    ∀ t ∈ U, IsCompact (modelFiber C t) ∧ (0:Space m) ∈ interior (modelFiber C t)}

/-- Closed logarithmic boxes agree exactly with the source definition. -/
def logarithmicBox (k : ℕ) (L : ℝ) : Set (Space k) := {x | ∀ i, |x i| ≤ L}

end RegularFiberDomain

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualLogMeasureFurther
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Filter Metric
open scoped Topology

/- The quantifier order in bounds.tex: every finite box has its own eventual
index. No common threshold for infinitely many boxes is needed. -/
def logarithmicCutoff (k : ℕ) (L : ℝ) (x : Space k) : ℝ :=
  ∏ i : Fin k, (1-Real.smoothTransition (x i-L))*(1-Real.smoothTransition (-x i-L))

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TiltedTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- Every coefficient of these covectors is positive, so their affine caps
are uniformly bounded in the orthant model. -/
def capTiltedCovector (r : ι) (i : ι) : ℝ := 1 + (Pi.single r (1:ℝ) : ι → ℝ) i

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SigmaCapHelpers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/-- The actual continuous linear forms chosen in bounds.tex256. -/
def capTiltedForm {k : ℕ} (j : Fin k) : Space k →L[ℝ] ℝ :=
  ∑ i, capTiltedCovector j i • EuclideanSpace.proj i
@[simp] lemma capTiltedForm_apply {k : ℕ} (j : Fin k) (s : Space k) :
    capTiltedForm j s = ∑ i, capTiltedCovector j i * s i := by
  simp [capTiltedForm, PiLp.proj_apply]
@[simp] lemma capTiltedForm_basis {k : ℕ} (j i : Fin k) :
    capTiltedForm j (EuclideanSpace.basisFun (Fin k) ℝ i) = capTiltedCovector j i := by
  simp [capTiltedForm_apply, EuclideanSpace.basisFun_apply]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NormalizedCellGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
section NormalizedSigmaDependencies

section NormalizedCellGeometry
open Metric
/-- The literal fixed cell of bounds.tex. -/
def normalizedCell (k : ℕ) : Set (Space k) := {s | ∀ i, s i ∈ Icc (1/2) 2}
/-- The open positive neighbourhood used for differentiating support functions. -/
def normalizedCellDomain (k : ℕ) : Set (Space k) := {s | ∀ i, s i ∈ Ioo (1/4) 4}

end NormalizedCellGeometry



end NormalizedSigmaDependencies
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_FlatProductCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {S E F : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

def flatProductCoordinates {n : ℕ} (bS : OrthonormalBasis ι ℝ S)
    (bF : OrthonormalBasis κ ℝ F) (e : Fin n ≃ ι ⊕ κ) : Space n ≃L[ℝ] (S × F) :=
  (((bS.prod bF).reindex e.symm).repr.symm.toContinuousLinearEquiv).trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ S F)

def flatProductFiberBasis (bF : OrthonormalBasis κ ℝ F)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) : OrthonormalBasis (κ ⊕ Unit) ℝ E :=
  (bF.prod (OrthonormalBasis.singleton Unit ℝ)).map f

def flatProductEmbedding (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) : (S × F) →L[ℝ] (S × E) :=
  (ContinuousLinearMap.fst ℝ S F).prod
    (f.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.inl ℝ F ℝ).comp (ContinuousLinearMap.snd ℝ S F))))

@[simp] lemma flatProductEmbedding_apply (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (q : S × F) :
    flatProductEmbedding f q = (q.1, f (WithLp.toLp 2 (q.2,0))) := rfl

@[simp] lemma flatProductFiberBasis_last (bF : OrthonormalBasis κ ℝ F)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) :
    flatProductFiberBasis bF f (Sum.inr ()) = f (WithLp.toLp 2 (0,(1:ℝ))) := by
  simp [flatProductFiberBasis,OrthonormalBasis.map_apply,OrthonormalBasis.prod_apply]

@[simp] lemma flatProductFiberBasis_first (bF : OrthonormalBasis κ ℝ F)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (j : κ) :
    flatProductFiberBasis bF f (Sum.inl j) = f (WithLp.toLp 2 (bF j,0)) := by
  simp [flatProductFiberBasis,OrthonormalBasis.map_apply,OrthonormalBasis.prod_apply]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricInverseMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- Covector contraction with the inverse second form is unchanged by an
invertible coordinate change. This uses the actual matrix inverse. -/
def parametricInverseMetric {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (X : Space n → E) (ν : E →L[ℝ] ℝ) (f : Space n → ℝ) (x : Space n) : ℝ :=
  inverseMatrixPair (parametricSecondForm X ν x)
    (fun i => dirDeriv (coordinateVector n i) f x)
    (fun i => dirDeriv (coordinateVector n i) f x)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualInverseMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology

def graphConormalAt {n : ℕ} (u : Space n → ℝ) (x : Space n) :
    (Space n × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ (Space n) ℝ) -
    (fderiv ℝ u x).comp (ContinuousLinearMap.fst ℝ (Space n) ℝ)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualFlatInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def pulledBaseGraphFunction {n : ℕ} (u : Space n → ℝ) (a : Space n × ℝ)
    (L : (S × E) ≃L[ℝ] (Space n × ℝ)) (ℓ : S →L[ℝ] ℝ) (x : Space n) : ℝ :=
  ℓ (L.symm ((x,u x)-a)).1

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_CapInverseBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/-- The literal inverse-Hessian norm of a restricted ambient affine covector. -/
def graphInverseMetric {n : ℕ} (u : Space n → ℝ)
    (a : Space n →L[ℝ] ℝ) (b d : ℝ) (x : Space n) : ℝ :=
  ∑ i, ∑ j, (hessian u x)⁻¹ i j *
    dirDeriv (coordinateVector n i) (graphAffineFunction u a b d) x *
    dirDeriv (coordinateVector n j) (graphAffineFunction u a b d) x

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_FixedBasisCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section FixedBasisCoordinates
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
def targetBasisCoordinates {n : ℕ} (b : Module.Basis (Fin n ⊕ Unit) ℝ G) :
    G ≃L[ℝ] (Space n × ℝ) :=
  (b.equiv (graphAmbientBasis n) (Equiv.refl _)).toContinuousLinearEquiv

end FixedBasisCoordinates

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_AmbientStraightening
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

def ambientCoordinates (n : ℕ) : (Space n × ℝ) ≃ₗ[ℝ] (Fin n ⊕ Unit → ℝ) :=
  (graphAmbientBasis n).equivFun

@[simp] lemma ambientCoordinates_inl {n : ℕ} (z : Space n × ℝ) (i : Fin n) :
    ambientCoordinates n z (Sum.inl i) = z.1 i := by
  simp [ambientCoordinates,graphAmbientBasis]

@[simp] lemma ambientCoordinates_inr {n : ℕ} (z : Space n × ℝ) (i : Unit) :
    ambientCoordinates n z (Sum.inr i) = z.2 := by
  simp [ambientCoordinates,graphAmbientBasis]

def ambientSwap {n : ℕ} (j : Fin n ⊕ Unit) : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ) :=
  ((ambientCoordinates n).trans ((LinearEquiv.funCongrLeft ℝ ℝ
    (Equiv.swap j (Sum.inr ()))).trans (ambientCoordinates n).symm)).toContinuousLinearEquiv

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_GraphBallArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

def graphAreaBoxBound (n : ℕ) (R : ℝ) : ℝ≥0∞ :=
  (2*n+1 : ℕ) * ((volume (Metric.closedBall (0 : Space n) n))^(1/((n:ℝ)+2)) *
    (volume (Metric.closedBall (0 : Space n) (n*R)))^(1-1/((n:ℝ)+2)))

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SmoothCapTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section SmoothCapTest

/-- A smooth convex cap test, quadratic below the fixed transition interval
and identically zero above it. -/
def smoothCapTest (ε b t : ℝ) : ℝ :=
  ∫ s in (-ε)..(b-t), smoothPositivePart ε s

end SmoothCapTest

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_AffineInvariantCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/-- The inward conormal of the actual affine-image graph, pulled back to its
original base. Its norm is NOT replaced by a vertical component. -/
def affineGraphConormal {n : ℕ} (u : Space n → ℝ)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (x : Space n) :
    (Space n × ℝ) →L[ℝ] ℝ :=
  ((ContinuousLinearMap.snd ℝ (Space n) ℝ) -
    (fderiv ℝ u x).comp (ContinuousLinearMap.fst ℝ (Space n) ℝ)).comp L.symm.toContinuousLinearMap

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TargetCapLIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The actual graph conormal expressed in an arbitrary fixed target space. -/
def targetGraphConormal {n : ℕ} (u : Space n → ℝ)
    (L : G ≃L[ℝ] (Space n × ℝ)) (x : Space n) : G →L[ℝ] ℝ :=
  ((ContinuousLinearMap.snd ℝ (Space n) ℝ) -
    (fderiv ℝ u x).comp (ContinuousLinearMap.fst ℝ (Space n) ℝ)).comp L.toContinuousLinearMap

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SphereIsometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open intervalIntegral
open scoped Pointwise

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def linearIsometrySphereHomeomorph (f : E ≃ₗᵢ[ℝ] F) :
    Metric.sphere (0:E) 1 ≃ₜ Metric.sphere (0:F) 1 :=
  f.toHomeomorph.sets (by ext x; simp)

@[simp] lemma linearIsometrySphereHomeomorph_coe (f : E ≃ₗᵢ[ℝ] F)
    (e : Metric.sphere (0:E) 1) :
    ((linearIsometrySphereHomeomorph f e : Metric.sphere (0:F) 1) : F) = f e := rfl

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_UniformSphericalCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open intervalIntegral
open scoped Pointwise

open Filter
open scoped Topology
/- Every admissible graph path has at least the Euclidean length of its
base displacement. This uses the literal C¹-path definition of completeness. -/
@[simp] theorem graphPathLength_neg {n : ℕ} (u : Space n → ℝ) (γ : ℝ → Space n) :
    graphPathLength (-u) γ = graphPathLength u γ := by
  unfold graphPathLength
  simp only [fderiv_neg, neg_apply, neg_sq]

@[simp] theorem graphEDist_neg {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (x y : Space n) : graphEDist Ω (-u) x y = graphEDist Ω u x y := by
  unfold graphEDist
  simp only [graphPathLength_neg]

/- The straight-segment estimate in its geometric form. Both possible
orientations of a monotone height are included. -/

open Filter
open scoped Topology

/- Intrinsic convergence always entails convergence of base points. -/

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SigmaNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
section DependencyScope
open Filter
open scoped Topology

section SigmaNormalization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- The genuine adjoint equivalence of a transverse linear normalization. -/
def adjointEquiv (A : E ≃L[ℝ] E) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.equivOfInverse' A.toContinuousLinearMap.adjoint
    A.symm.toContinuousLinearMap.adjoint
    (by rw [← ContinuousLinearMap.adjoint_comp];
        have h : A.symm.toContinuousLinearMap.comp A.toContinuousLinearMap =
            ContinuousLinearMap.id ℝ E := by ext x; simp
        rw [h,ContinuousLinearMap.adjoint_id])
    (by rw [← ContinuousLinearMap.adjoint_comp];
        have h : A.toContinuousLinearMap.comp A.symm.toContinuousLinearMap =
            ContinuousLinearMap.id ℝ E := by ext x; simp
        rw [h,ContinuousLinearMap.adjoint_id])

end SigmaNormalization


end DependencyScope


end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_UniformActualCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section UniformActualCells
open Filter Metric

/-- The multiplicative cell with positive center `s`, exactly the cell of
bounds.tex:219: no choice of transverse normalization occurs in this set. -/
def multiplicativeCell {k : ℕ} (s : Space k) : Set (Space k) :=
  {x | ∀ i, s i / 2 ≤ x i ∧ x i ≤ 2*s i}

end UniformActualCells


end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_UniformLogCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section UniformLogCells
open Metric Filter

/-- Closed unit cells in the actual logarithmic base coordinates. -/
def logarithmicUnitCell (k : ℕ) (z : Fin k → ℤ) : Set (Space k) :=
  {x | ∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ (z i : ℝ)+1}

end UniformLogCells


end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ProductAmbientCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

def productAmbientBasis {n k : ℕ} (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (e : Fin n ≃ Fin k ⊕ κ) : Module.Basis (Fin n ⊕ Unit) ℝ (Space k × E) :=
  ((EuclideanSpace.basisFun (Fin k) ℝ).toBasis.prod bE.toBasis).reindex
    ((Equiv.sumCongr e (Equiv.refl Unit)).trans (Equiv.sumAssoc (Fin k) κ Unit)).symm

def productBaseIndex {n k : ℕ} (e : Fin n ≃ Fin k ⊕ κ) (i : Fin k) : Fin n ⊕ Unit :=
  ((Equiv.sumCongr e (Equiv.refl Unit)).trans (Equiv.sumAssoc (Fin k) κ Unit)).symm (Sum.inl i)

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_FiniteProjectiveCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {τ : Type*} [Fintype τ]

def projectiveAxis (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) : E :=
  f (WithLp.toLp 2 (0,(1:ℝ)))

def projectiveFrameAt (b : OrthonormalBasis τ ℝ E)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (j : τ) : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E :=
  f.trans (Submodule.reflection (ℝ ∙ (projectiveAxis f - b j))ᗮ)

def signedProjectiveFrame (b : OrthonormalBasis τ ℝ E)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (j : τ × Bool) : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E :=
  if j.2 then projectiveFrameAt b f j.1 else
    (projectiveFrameAt b f j.1).trans (LinearIsometryEquiv.neg ℝ)

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_AffineStripArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter
open scoped Topology

def verticalScale {n : ℕ} (c : ℝ) (hc : c ≠ 0) :
    (Space n × ℝ) ≃L[ℝ] (Space n × ℝ) :=
  ({ toFun := fun z => (z.1,c*z.2)
     invFun := fun z => (z.1,c⁻¹*z.2)
     map_add' := by intro x y; ext <;> simp [mul_add]
     map_smul' := by intro t x; ext <;> simp [mul_left_comm]
     left_inv := by intro z; ext <;> simp [hc]
     right_inv := by intro z; ext <;> simp [hc] } :
    (Space n × ℝ) ≃ₗ[ℝ] (Space n × ℝ)).toContinuousLinearEquiv

@[simp] lemma verticalScale_apply {n : ℕ} (c : ℝ) (hc : c ≠ 0) (z : Space n × ℝ) :
    verticalScale c hc z = (z.1,c*z.2) := rfl

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_GeneralCapCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section GeneralCapCoordinates

/- A fixed genuine invertible coordinate map with the prescribed height
functional. The product max norm is retained; no artificial inner-product
instance is introduced on these coordinates. -/
def affineImageLinearCapArea {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
    (ell : (Space n × ℝ) →L[ℝ] ℝ) (b : ℝ) : ℝ :=
  Real.rpow |L.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2)) *
    ∫ x in {x | x ∈ Ω ∧ ell (L (x,u x)+v) < b}, affineAreaDensity u x

end GeneralCapCoordinates

open Filter Metric
open scoped Topology

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_OrthantGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter
open scoped Topology

open Filter Metric
open scoped Topology

def ambientOrthant (n : ℕ) : Set (Space n × ℝ) :=
  {z | ∀ i, 0 ≤ ambientCoordinates n z i}

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_OrthantHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter
open scoped Topology

open Filter Metric
open scoped Topology

def orthantHeight (n : ℕ) : (Space n × ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin n ⊕ Unit, (ContinuousLinearMap.proj i).comp
    (ambientCoordinates n).toContinuousLinearEquiv.toContinuousLinearMap

def orthantCenter (n : ℕ) : Space n × ℝ :=
  (ambientCoordinates n).symm (fun _ => 1)

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ModelPositiveSigma
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section ModelPositiveSigma
open Metric Filter

def positiveClosedRectangle {k : ℕ} (a b : ℝ) : Set (Space k) :=
  {s | ∀ i, a ≤ s i ∧ s i ≤ b}

end ModelPositiveSigma


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ModelCenteringFurther
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter Metric
open scoped Topology Pointwise
open scoped Pointwise
open scoped Pointwise

open Filter
open scoped Topology

/- Intrinsic convergence always entails convergence of base points. -/
/- Completeness prevents a finite base endpoint from being lost when graph
paths make a sequence intrinsically Cauchy. -/
/- A chord bound along a family of segments turns ordinary Cauchy control of
base and height into control for the actual graph metric. -/
/- Restricting a monotone-height ray to any oriented subsegment gives the
uniform chord bound used to exhibit an intrinsic Cauchy tail. -/
/- A bounded ray with monotone graph height cannot end at a missing finite
base point of a complete graph. This proves the metric step rather than
assuming properness of the embedding. -/
/- A differentiable convex function on a finite half-open interval has a
monotone tail (in one of the two orientations). -/
/- The tangent line at the initial point bounds a convex ray from below,
so an upper bound on a finite ray implies a two-sided bound. -/
/- Completeness forbids any bounded convex ray from reaching a missing finite
endpoint. Convexity and two-sided variation, not a growth hypothesis, produce
the required metric Cauchy sequence. -/
/- The metric obstruction applied to an arbitrary bounded-height sequence,
not merely points already lying on a fixed ray. This is the core boundary
properness argument in geometry.tex:36–55. -/
/- Actual height sublevels are closed in the ambient base space. No convex
extension of u to missing boundary points is used. -/
/- Finite boundary blow-up, derived from the manuscript's literal Euclidean
intrinsic completeness assumption. -/
/- The epigraph is genuinely closed in Rⁿ × R. Completeness was not
silently replaced by properness of the graph embedding. -/
/- Strict version of the second-derivative test, with specified derivatives. -/
def tangentHeight {n : ℕ} (u : Space n → ℝ) (a x : Space n) : ℝ :=
  u x - u a - fderiv ℝ u a (x - a)

@[simp] theorem tangentHeight_self {n : ℕ} (u : Space n → ℝ) (a : Space n) :
    tangentHeight u a a = 0 := by simp [tangentHeight]

def tangentSection {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (a : Space n) (t : ℝ) : Set (Space n) :=
  {x | x ∈ Ω ∧ tangentHeight u a x < t}

/- For positive height the closed sublevel is precisely the closure of the
open tangent section. Completeness supplies closedness; convexity supplies
approximation from the section interior. -/
def SectionBalance {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ) (ρ : ℝ) : Prop :=
  ∀ a ∈ Ω, ∀ t : ℝ, 0 < t → ∀ x ∈ closure (tangentSection Ω u a t),
    a - ρ • (x - a) ∈ closure (tangentSection Ω u a t)

/- A direct form of the closed-section reflection, with arbitrary finite
height (zero included). No balance conclusion is assumed about the domain. -/
def modulusIterates (ρ R r : ℝ) : ℕ :=
  ⌈Real.logb (1 + ρ / 2) ((2 * R / ρ) / r)⌉₊

/- Exact lower modulus b(r)=1/(8 A^N(r)) from the manuscript. -/
def normalizedModulus (ρ R r : ℝ) : ℝ :=
  1 / (8 * (((2 + ρ) * (1 + ρ) / ρ) ^ modulusIterates ρ R r))

def tangentModelEquiv {n : ℕ} (u : Space n → ℝ) (a : Space n) :
    (Space n × ℝ) ≃ᴬ[ℝ] (Space 1 × Space n) := by
  letI : ContinuousSMul ℝ (Space 1 × Space n) := Prod.continuousSMul
  let L : (Space n × ℝ) ≃L[ℝ] (Space 1 × Space n) := LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p => (WithLp.toLp 2 (fun _ => p.2 - fderiv ℝ u a p.1), p.1)
      invFun := fun q => (q.2, q.1 0 + fderiv ℝ u a q.2)
      left_inv := by intro p; dsimp; ext <;> simp
      right_inv := by
        intro q
        apply Prod.ext
        · ext i
          simp [Subsingleton.elim i (0 : Fin 1)]
        · rfl
      map_add' := by
        intro p q
        ext i <;> simp [map_add]
        ring
      map_smul' := by intro r p; ext i <;> simp [map_smul, mul_sub] }
  exact (ContinuousAffineEquiv.constVAdd ℝ (Space n × ℝ) (-(a,u a))).trans L.toContinuousAffineEquiv

@[simp] theorem tangentModelEquiv_apply {n : ℕ} (u : Space n → ℝ) (a x : Space n) (z : ℝ) :
    tangentModelEquiv u a (x,z) =
      (WithLp.toLp 2 (fun _ : Fin 1 => z-u a-fderiv ℝ u a (x-a)), x-a) := by
  change (WithLp.toLp 2 (fun _ : Fin 1 => (-u a+z)-fderiv ℝ u a (-a+x)), -a+x) = _
  simp only [neg_add_eq_sub]

@[simp] theorem tangentModelEquiv_fst {n : ℕ} (u : Space n → ℝ) (a : Space n)
    (p : Space n × ℝ) (i : Fin 1) :
    (tangentModelEquiv u a p).1 i = p.2-u a-fderiv ℝ u a (p.1-a) := by
  cases p
  simp only [tangentModelEquiv_apply]

@[simp] theorem tangentModelEquiv_snd {n : ℕ} (u : Space n → ℝ) (a : Space n)
    (p : Space n × ℝ) : (tangentModelEquiv u a p).2 = p.1-a := by
  cases p
  simp only [tangentModelEquiv_apply]

/- Completeness supplies an actual one-direction model in the affine family. -/

@[simp] theorem tangent_model_fiber {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (a : Space n) (t : ℝ) :
    modelFiber (tangentModelEquiv u a '' sourceEpigraph Ω u)
      (WithLp.toLp 2 (fun _ : Fin 1 => t)) =
      (fun x => x-a) '' {x | x ∈ Ω ∧ tangentHeight u a x ≤ t} := by
  ext y
  constructor
  · rintro ⟨⟨x,z⟩,⟨hx,hz⟩,he⟩
    have he1 := congrArg (fun q : Space 1 × Space n => q.1 0) he
    have he2 := congrArg Prod.snd he
    simp only [tangentModelEquiv_fst] at he1
    simp only [tangentModelEquiv_snd] at he2
    refine ⟨x,⟨hx,?_⟩,he2⟩
    change z-u a-fderiv ℝ u a (x-a) = t at he1
    dsimp [tangentHeight]
    linarith
  · rintro ⟨x,⟨hx,hxt⟩,rfl⟩
    refine ⟨(x,t+u a+fderiv ℝ u a (x-a)),⟨hx,?_⟩,?_⟩
    · dsimp [tangentHeight] at hxt
      linarith
    · ext i <;> simp [tangentModelEquiv_apply]
      ring

/- A model's direction number is bounded by the actual ambient dimension,
using an invertible affine map from its approximating sequence. -/

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_MaximalModelExclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section MaximalModelExclusion
/-- Choose orthonormal transverse coordinates without changing the Euclidean
norm used by the spherical fiber estimates. -/
def transverseEuclideanIsometry {m d : ℕ} (hmd : m = d+1) :
    WithLp 2 (Space d × ℝ) ≃ₗᵢ[ℝ] Space m := by
  have hdim : Module.finrank ℝ (WithLp 2 (Space d × ℝ)) = m := by
    rw [(WithLp.linearEquiv 2 ℝ (Space d × ℝ)).finrank_eq]
    simp [Module.finrank_prod,finrank_euclideanSpace,hmd]
  exact ((stdOrthonormalBasis ℝ (WithLp 2 (Space d × ℝ))).reindex (finCongr hdim)).repr

end MaximalModelExclusion


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_EntireAndDoubling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Filter
open scoped Topology

/-- The logarithm is taken only on the positive Hessian determinant at points
where the estimates are asserted. Outside the domain this is just a total function. -/
def logHessianDet {n : ℕ} (u : Space n → ℝ) (x : Space n) : ℝ :=
  Real.log (hessian u x).det

/-- The actual inverse-Hessian linearized operator, without the harmless
positive determinant factor in the frozen original PDE. -/
def inverseHessianTrace {n : ℕ} (u f : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian f x i j

def inverseHessianPair {n : ℕ} (u f g : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i, ∑ j, (hessian u x)⁻¹ i j *
    dirDeriv (coordinateVector n i) f x * dirDeriv (coordinateVector n j) g x

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_LogDetGradientEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section LogDetGradientEnergy

/-- Half the squared Euclidean gradient, expressed in the frozen orthonormal coordinates. -/
def gradientEnergy {n : ℕ} (u : Space n → ℝ) (x : Space n) : ℝ :=
  (1/2 : ℝ) * ∑ k, (dirDeriv (coordinateVector n k) u x)^2

end LogDetGradientEnergy

end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_LogBarrierCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section LogBarrierCalculus
open Filter
open scoped Topology

/-- Literal log-determinant barrier. On a negative section its logarithmic
cutoff is exactly `log (-u)`, because the real logarithm uses absolute value. -/
def affineDetBarrier {n : ℕ} (u : Space n → ℝ) (β γ : ℝ) (x : Space n) : ℝ :=
  logHessianDet u x + β * Real.log (u x) + γ * gradientEnergy u x

end LogBarrierCalculus


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_PositiveMatrixTraceBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

def gradientSquared {n : ℕ} (u : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ k, (dirDeriv (coordinateVector n k) u x)^2

def gradientHessianSquare {n : ℕ} (u : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ k, dirDeriv (coordinateVector n k) u x * dirDeriv (coordinateVector n k) (gradientEnergy u) x

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_DetBarrierPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section DetBarrierPhase

/-- Continuous phase whose logarithm is the maximum-principle barrier on a
negative section; the phase vanishes, rather than diverging, on its boundary. -/
def affineDetPhase {n : ℕ} (u : Space n → ℝ) (γ : ℝ) (x : Space n) : ℝ :=
  (hessian u x).det * (-u x)^(n+2) * Real.exp (γ * gradientEnergy u x)

end DetBarrierPhase


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ABPMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Filter
open scoped Topology

/-- A closed set large enough to contain every lower supporting point. -/
def abpContactSet {n : ℕ} (K : Set (Space n)) (f : Space n → ℝ) : Set (Space n) :=
  {x | x ∈ K ∧ f x ≤ 0 ∧ ∀ v : Space n, 0 ≤ fderiv ℝ (fderiv ℝ f) x v v}

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_DualHeightCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section DualHeightCalculus
open Filter
open scoped Topology

/-- Legendre tangent height pulled back by the actual gradient. No global
Legendre transform or assumed dual regularity is needed for these identities. -/
def dualHeight {n : ℕ} (u : Space n → ℝ) (x : Space n) : ℝ := tangentHeight u x 0

def positionEnergy {n : ℕ} (x : Space n) : ℝ := (1/2:ℝ) * ∑ k, (x k)^2

def positionSquared {n : ℕ} (x : Space n) : ℝ := ∑ k, (x k)^2

end DualHeightCalculus


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_DualDetBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section DualDetBarrier
open Filter
open scoped Topology

def dualCutoff {n : ℕ} (u : Space n → ℝ) (h : ℝ) (x : Space n) : ℝ := dualHeight u x - h

def dualDetBarrier {n : ℕ} (u : Space n → ℝ) (h β γ : ℝ) (x : Space n) : ℝ :=
  (-1:ℝ)*logHessianDet u x + β*Real.log (dualCutoff u h x) + γ*positionEnergy x

end DualDetBarrier


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_DualDetPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section DualDetPhase

/-- The pullback of the dual determinant phase to primal coordinates. -/
def dualDetPhase {n : ℕ} (u : Space n → ℝ) (h γ : ℝ) (x : Space n) : ℝ :=
  ((hessian u x).det)⁻¹ * (-dualCutoff u h x)^(n+2) * Real.exp (γ * positionEnergy x)

end DualDetPhase


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TangentShiftCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section TangentShiftCalculus
open Filter
open scoped Topology

/-- Subtract the tangent plane and a positive section height; this does not
alter the Hessian, hence preserves the original classical PDE. -/
def tangentShift {n : ℕ} (f : Space n → ℝ) (a : Space n) (h : ℝ) (x : Space n) : ℝ :=
  tangentHeight f a x - h

end TangentShiftCalculus


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NormalizedDet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section NormalizedDetProducer

/-- Prescribed lower modulus of tangent sections; this is the same section
condition as rigidity.tex, with the frozen `tangentSection` definition. -/
def HasLowerSectionModulus {n : ℕ} (O : Set (Space n)) (f : Space n → ℝ)
    (b : ℝ → ℝ) : Prop :=
  ∀ x ∈ O, ∀ r : ℝ, 0 < r → tangentSection O f x (b r) ⊆ Metric.ball x r

end NormalizedDetProducer



end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NormalizedLogVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section NormalizedLogVariance

/-- Literal normalized solution data, produced by the actual centered section maps. -/
structure BalancedNormalized {n : ℕ} (ρ R : ℝ) (v : Space n → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ v
  posDef : ∀ x, (hessian v x).PosDef
  maximal : AffineMaximalOn univ v
  zero : v 0 = 0
  deriv_zero : fderiv ℝ v 0 = 0
  balance : SectionBalance univ v ρ
  inner : Metric.ball 0 1 ⊆ tangentSection univ v 0 1
  outer : tangentSection univ v 0 1 ⊆ Metric.ball 0 R

end NormalizedLogVariance


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_LinearNormalizationCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section LinearNormalizationCalculus

/-- The actual square matrix in the frozen Euclidean coordinates. -/
def cleMatrix {n : ℕ} (A : Space n ≃L[ℝ] Space n) : Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).symm A.toContinuousLinearMap

@[simp] lemma cleMatrix_apply {n : ℕ} (A : Space n ≃L[ℝ] Space n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (cleMatrix A) = A.toContinuousLinearMap := by
  exact (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).apply_symm_apply _

/-- Center-preserving horizontal normalization and positive vertical scaling. -/
def normalizedFunction {n : ℕ} (u : Space n → ℝ) (A : Space n ≃L[ℝ] Space n)
    (t : ℝ) (y : Space n) : ℝ := t⁻¹ * u (A y)

end LinearNormalizationCalculus


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ConstantDetCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section ConstantDetCalculus
open Filter Matrix
open scoped Topology

/-- Entrywise derivative of a genuine smooth matrix field. -/
def matrixDirDeriv {n m : ℕ} (v : Space n) (A : Space n → Matrix (Fin m) (Fin m) ℝ)
    (x : Space n) : Matrix (Fin m) (Fin m) ℝ := fun i j => dirDeriv v (fun y => A y i j) x

end ConstantDetCalculus


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_DirectionalJacobi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section DirectionalJacobi
open Matrix

/-- A convenient exact representation of the reciprocal n-th root, always
used on a strictly positive directional Hessian. -/
def inverseNthRoot (n : ℕ) (f : Space n → ℝ) (x : Space n) : ℝ :=
  Real.exp (-((n:ℝ)⁻¹)*Real.log (f x))

end DirectionalJacobi


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_QuadraticAffineImage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Matrix

def paraboloidLinearEquiv {n : ℕ} (L : Space n ≃ₗ[ℝ] Space n)
    (ℓ : Space n →L[ℝ] ℝ) : (Space n × ℝ) ≃ₗ[ℝ] (Space n × ℝ) where
  toFun p := (L.symm p.1,(1/2:ℝ)*p.2+ℓ (L.symm p.1))
  invFun p := (L p.1,2*(p.2-ℓ p.1))
  left_inv := by
    intro p
    apply Prod.ext
    · simp
    · ring
  right_inv := by
    intro p
    apply Prod.ext
    · simp
    · simp only [LinearEquiv.symm_apply_apply]
      ring
  map_add' := by
    intro p q
    apply Prod.ext
    · simp
    · simp only [Prod.fst_add,Prod.snd_add,map_add]
      ring
  map_smul' := by
    intro a p
    apply Prod.ext
    · simp
    · change (1/2:ℝ)*(a*p.2)+ℓ (L.symm (a • p.1)) = a*((1/2:ℝ)*p.2+ℓ (L.symm p.1))
      rw [map_smul,map_smul]
      simp only [smul_eq_mul]
      ring

end AffineBernstein

end

end OAI
end


