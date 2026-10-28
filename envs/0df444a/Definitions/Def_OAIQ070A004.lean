-- Prove2me | Definitions.Def_OAIQ070A004
-- name    : OAIQ070A004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T11:17:15.968622+00:00
-- url     : https://prove2.me/theorems/4ebc636e-76a3-424e-bbbb-d1b64254454b
-- title:
--   Definitions bundle OAIQ070A004 of the split of OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 165 declarations of OpenAI's Lean: 126 definitions, 4 instances and 35 theorems. The definitions and types are `OAI.YauCounterexamples.continuousMapApply`, `OAI.YauCounterexamples.continuousMapApplyCLM`, `OAI.YauCounterexamples.coordinateDivergence`, `OAI.YauCounterexamples.coordinateGradientPair`, `OAI.YauCounterexamples.coordinateMetricFirstCoefficient`, `OAI.YauCounterexamples.cutoffFactor`, `OAI.YauCounterexamples.directionalJet`, `OAI.YauCounterexamples.dualNorm`, `OAI.YauCounterexamples.dualSpace`, `OAI.YauCounterexamples.expJetConstant`, `OAI.YauCounterexamples.fiberOpenPartialHomeomorph`, `OAI.YauCounterexamples.finiteTaylorFunction`, `OAI.YauCounterexamples.finiteWaveAmplitude`, `OAI.YauCounterexamples.finiteWaveSuperposition`, `OAI.YauCounterexamples.fourCircleCoord`, `OAI.YauCounterexamples.fourTailHeadEquiv`, `OAI.YauCounterexamples.fourTailHeadLinear`, `OAI.YauCounterexamples.frameDualSpace`, `OAI.YauCounterexamples.gaussianDualNorm`, `OAI.YauCounterexamples.gaussianDualSpace`, `OAI.YauCounterexamples.gaussianFormNorm`, `OAI.YauCounterexamples.gaussianPairOppositeProbability`, `OAI.YauCounterexamples.gaussianPairSignProduct`, `OAI.YauCounterexamples.genericHessMapSpace`, `OAI.YauCounterexamples.globalPrepDualNorm`, `OAI.YauCounterexamples.globalPrepDualSpace`, `OAI.YauCounterexamples.gridPoint`, `OAI.YauCounterexamples.hessianFromJet`, `OAI.YauCounterexamples.hmoDualNorm`, `OAI.YauCounterexamples.hmoDualSpace`, `OAI.YauCounterexamples.hmsDualNorm`, `OAI.YauCounterexamples.intrinsicForwardMapNorm`, `OAI.YauCounterexamples.inverseFrequency`, `OAI.YauCounterexamples.jetDualNorm`, `OAI.YauCounterexamples.jetDualSpace`, `OAI.YauCounterexamples.leadingComplexJet`, `OAI.YauCounterexamples.lpProductFunction`, `OAI.YauCounterexamples.lpProductIsometry`, `OAI.YauCounterexamples.lpProductLinearMap`, `OAI.YauCounterexamples.maskComplex` and 86 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `SmoothYau_DifferentialEq_HmoDualNorm`, `SmoothYau_DifferentialEq_MixedJacobianMatrix`, `SmoothYau_Estimates_ClmMatrixAlgHom`, `SmoothYau_Estimates_ComplexGaussianRealValue`, `SmoothYau_Estimates_GeneratedCutoffWaveEndpointRatio`, `SmoothYau_Estimates_GridPoint`, `SmoothYau_Estimates_LocalizedPacketSignProbability`, `SmoothYau_Estimates_MiddleBox`, `SmoothYau_Estimates_PathExtension`, `SmoothYau_Estimates_RescaledDifferentialPerturbation`, `SmoothYau_Geometry_ConformalMetric`, `SmoothYau_Geometry_CoordinateMetricFirstCoefficient`, `SmoothYau_Geometry_MetricGradient`, `SmoothYau_Geometry_PinnedMetricJointGradientPair`, `SmoothYau_Geometry_PrepDualNorm`, `SmoothYau_Geometry_RadialFiniteDualNorm`, `SmoothYau_Geometry_RoundMetricExists`, `SmoothYau_Geometry_ThreeDirectionsNormedSpace`, `SmoothYau_Limits_CoordinateForm`, `SmoothYau_Limits_ExistsCompactSignedEnvelope`, `SmoothYau_Limits_FrameDualNorm`, `SmoothYau_Limits_OscDualNorm`, `SmoothYau_Limits_PlanePairMap`, `SmoothYau_Limits_RealMatrixCauchy`, `SmoothYau_Limits_ScalarCauchyCross`, `SmoothYau_Limits_SphericalFixedFormNorm`, `SmoothYau_NodalMeasure_ExtrusionEquiv`, `SmoothYau_NodalMeasure_SphericalNodalFinite`, `SmoothYau_ProductMetric_FourWaveThreeSmul`, `SmoothYau_Smoothness_ComplexPolarWeight`, `SmoothYau_Smoothness_ContDiffPartialIteratedFDeriv`, `SmoothYau_Smoothness_ContDiffSmoothFiniteWave`, `SmoothYau_Smoothness_ContinuousCompactSmoothJets`, `SmoothYau_Smoothness_CoordinateMetricFlux`, `SmoothYau_Smoothness_FamilyInverseFst`, `SmoothYau_Smoothness_FlowParameters`, `SmoothYau_Smoothness_FourLiftThreeSmul`, `SmoothYau_Smoothness_GlobalPrepDualNorm`, `SmoothYau_Smoothness_HessianJet`, `SmoothYau_Smoothness_LinearPowerDirectional`, `SmoothYau_Smoothness_LocalIntegrationParts`, `SmoothYau_Smoothness_LpProductLinearMap`, `SmoothYau_Smoothness_MultilinearPolynomial`, `SmoothYau_Smoothness_NormIteratedFDerivCompLinear`, `SmoothYau_Smoothness_NormIteratedFDerivScalarDirection`, `SmoothYau_Smoothness_NormalChartWave`, `SmoothYau_Smoothness_NormalInverseVecNorm`, `SmoothYau_Smoothness_NormalJetMapFirstPhase`, `SmoothYau_Smoothness_ProductSphereFstPower`, `SmoothYau_Smoothness_ProfilePeriodizeEventuallyZero`, `SmoothYau_Smoothness_PulledGradient`, `SmoothYau_Smoothness_RoundPowerRadius`, `SmoothYau_Smoothness_SmDualNorm`, `SmoothYau_Smoothness_ThreeFirstNormedSpace`, `SmoothYau_Spectrum_ContinuousRealQuadraticCoerciveNear`, `SmoothYau_Spectrum_FiniteWaveAmplitude`, `SmoothYau_Spectrum_NormIteratedFDerivConstMul`, `SmoothYau_Spectrum_ProductFrequencyTop`, `SmoothYau_Spectrum_ScalarCompDirectional`, `SmoothYau_Spectrum_SphereProjection`, `SmoothYau_Spectrum_ThreeCoupledNormedSpace`, `SmoothYau_Spectrum_UnitSphereProjection`, `SmoothYau_SphereMetric_RadialBaseEnvelope`, `SmoothYau_SphereMetric_ThreeFormulaNormedSpace`, `SmoothYau_SphereMetric_ThreeRobustProfileNormedSpace`, `SmoothYau_SphereMetric_UnitCorrelation`.
--
--   **Imports.** It imports the published bundle `Def_SmoothYau`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ070A007` and `OAIQ070A008`; the statements `OAI_YauCounterexamples_CompactMetricAtlas_eventually_positive_factor_of_jets`, `OAI_YauCounterexamples_CompactMetricAtlas_eventually_product_positive_factor_of_eventual_jets`, `OAI.YauCounterexamples.CompactMetricAtlas.global_cutoff_raw_controls`, `OAI_YauCounterexamples_MetricIntegralAtlas_green`, `OAI.YauCounterexamples.common_near_wave_sign_probability`, `OAI_YauCounterexamples_cutoff_raw_bounded_by_near_one`, `OAI.YauCounterexamples.finiteWaveSuperposition_residual`, `OAI_YauCounterexamples_laplaceBeltrami_self_any_basis`, `OAI_YauCounterexamples_local_eigen_proportional_of_annular_rank`, `OAI_YauCounterexamples_local_eigen_proportional_of_gradient_rank`, `OAI_YauCounterexamples_productSphere_fstPower_trace`, `OAI.YauCounterexamples.productSphere_power_trace`, `OAI.YauCounterexamples.productSphere_sndPower_trace`, `OAI_YauCounterexamples_regular_quotient_at_zero`, `OAI.YauCounterexamples.spherical_cutoff_control_bounds`, `OAI.YauCounterexamples.three_cutoff_control_bounds`, `OAI_YauCounterexamples_three_cutoff_raw_bounded_by_near_one` and `OAI_YauCounterexamples_three_regular_quotient_at_zero`; the proofs of `OAI.YauCounterexamples.common_near_wave_sign_probability`, `OAI_YauCounterexamples_compactSmooth_complete`, `OAI_YauCounterexamples_cutoff_raw_bounded_by_near_one`, `OAI.YauCounterexamples.finite_near_far_sign_probability`, `OAI_YauCounterexamples_gaussian_uniform_polynomial_smallBall`, `OAI.YauCounterexamples.laplaceBeltrami_any_basis_univ`, `OAI_YauCounterexamples_local_eigen_proportional_of_annular_rank`, `OAI_YauCounterexamples_local_eigen_proportional_of_gradient_rank`, `OAI.YauCounterexamples.nodalMeasure_coordinates_lower_bound`, `OAI_YauCounterexamples_productSphere_fstPower_trace`, `OAI.YauCounterexamples.productSphere_power_trace`, `OAI.YauCounterexamples.productSphere_sndPower_trace`, `OAI_YauCounterexamples_regular_quotient_at_zero`, `OAI.YauCounterexamples.spherical_cutoff_control_bounds`, `OAI.YauCounterexamples.three_cutoff_control_bounds`, `OAI_YauCounterexamples_three_cutoff_raw_bounded_by_near_one` and `OAI_YauCounterexamples_three_regular_quotient_at_zero`.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 1581d4c

import Mathlib
import Definitions.Def_SmoothYau

section
-- module Solutions.OAIQ070_YAU.Compat
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
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CoordinateForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance dualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance dualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_DifferentialEq_HmoDualNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology InnerProductSpace
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance hmoDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance hmoDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_DifferentialEq_MixedJacobianMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace YauCounterexamples
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def mixed_jacobianMatrix (b c : Module.Basis ι ℝ E) (f : E → E) (x : E) : Matrix ι ι ℝ :=
  LinearMap.toMatrix b c (fderiv ℝ f x).toLinearMap

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ClmMatrixAlgHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open scoped Matrix.Norms.Operator
open scoped Matrix.Norms.Operator
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def matrixOfForm (b : Module.Basis ι ℝ E) (G : E →L[ℝ] E →L[ℝ] ℝ) : Matrix ι ι ℝ :=
  fun i j => G (b i) (b j)


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_MultilinearPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def directionalJet : List E → (E → F) → E → F
  | [], f => f
  | v :: l, f => fun x => fderiv ℝ (directionalJet l f) x v

@[simp] theorem directionalJet_nil (f : E → F) : directionalJet [] f = f := rfl
@[simp] theorem directionalJet_cons (v : E) (l : List E) (f : E → F) :
    directionalJet (v :: l) f = fun x => fderiv ℝ (directionalJet l f) x v := rfl

def finiteTaylorFunction (f : E → F) (N : ℕ) (x : E) : F :=
  ∑ j ∈ Finset.range N, (j.factorial : ℝ)⁻¹ •
    iteratedFDeriv ℝ j f 0 (fun _ => x)


end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff

open MvPolynomial
variable {σ : Type*}

variable [Fintype σ]

def realPolyDerivEmbed (i : σ) : ℂ →L[ℝ] ((σ → ℝ) →L[ℝ] ℂ) :=
  ContinuousLinearMap.smulRightL ℝ (σ → ℝ) ℂ (ContinuousLinearMap.proj i)

@[simp] theorem realPolyDerivEmbed_apply (i : σ) (c : ℂ) (v : σ → ℝ) :
    realPolyDerivEmbed i c v = (v i : ℂ) * c := by
  simp [realPolyDerivEmbed, Complex.real_smul]


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_HessianJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance gaussianDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance gaussianDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance gaussianFormNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
section SecondJetBridge
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def hessianFromJet : (E [×2]→L[ℝ] F) →L[ℝ] (E →L[ℝ] E →L[ℝ] F) :=
  ((continuousMultilinearCurryFin1 ℝ E F).toContinuousLinearEquiv.toContinuousLinearMap.postcomp E).comp
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) F).toContinuousLinearEquiv.toContinuousLinearMap

end SecondJetBridge



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ContinuousRealQuadraticCoerciveNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace YauCounterexamples

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def transverseProjection (ν b : E) : E := b - inner ℝ ν b • ν

def normalizedTransverse (a ν b : E) : E :=
  (Real.sqrt (1 + ‖a‖^2) / ‖transverseProjection ν b‖) • transverseProjection ν b

@[fun_prop] lemma continuous_transverseProjection :
    Continuous (fun p : E × E => transverseProjection p.1 p.2) := by
  unfold transverseProjection
  fun_prop

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_NormIteratedFDerivConstMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def expJetConstant (k : ℕ) (C : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) * i.factorial * C ^ i

end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ProfilePeriodizeEventuallyZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff

def radialPrimitive (β : ℝ → ℝ) (s : ℝ) : ℝ := ∫ t in (0:ℝ)..s, β t


end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_MetricGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI





noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

omit [FiniteDimensional ℝ E] in
lemma positive_bilinear_unique (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ z : E, z ≠ 0 → 0 < B z z) (v w : E)
    (h : ∀ z, B v z = B w z) : v = w := by
  by_contra hn
  have hp := hB (v - w) (sub_ne_zero.mpr hn)
  have hz : B (v - w) (v - w) = 0 := by
    rw [map_sub B v w, sub_apply, h, sub_self]
  linarith

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_PulledGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
section GenericCoordinateHessian
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
local instance genericHessMapSpace : NormedSpace ℝ (E →L[ℝ] V) := inferInstance

end GenericCoordinateHessian


end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff
open scoped InnerProductSpace
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

def pulledGradient (j : V →L[ℝ] E) (u : E → ℝ) (x : E) : V :=
  (InnerProductSpace.toDual ℝ V).symm ((fderiv ℝ u x).comp j)



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_NormalJetMapFirstPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance normalDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance normalDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance normalFormNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance normalFormSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def normalJetMap (p : E) (A : E →L[ℝ] E) (C : E →L[ℝ] E →L[ℝ] E) (x : E) : E :=
  p + A x - (1 / 2 : ℝ) • C x x


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Manifold
open scoped Topology ContDiff


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_FrameDualNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance frameDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_PathExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def pathExtension (u : C(unitInterval, E)) : C(ℝ, E) :=
  u.comp ⟨projIcc 0 1 zero_le_one, continuous_projIcc⟩

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[simp] lemma pathExtension_apply (u : C(unitInterval, E)) (t : ℝ) :
    pathExtension u t = u (projIcc 0 1 zero_le_one t) := rfl

def volterra : C(unitInterval, E) →L[ℝ] C(unitInterval, E) := by
  let L : C(unitInterval, E) →ₗ[ℝ] C(unitInterval, E) :=
    { toFun := fun u => ⟨fun s => ∫ t in 0..(s : ℝ), pathExtension u t,
        (continuous_primitive (fun a b => (pathExtension u).continuous.intervalIntegrable a b) 0).comp
          continuous_subtype_val⟩
      map_add' := fun u v => by
        ext s
        exact integral_add ((pathExtension u).continuous.intervalIntegrable _ _)
          ((pathExtension v).continuous.intervalIntegrable _ _)
      map_smul' := fun c u => by ext s; exact integral_smul c (pathExtension u) }
  apply L.mkContinuous 1
  intro u
  rw [one_mul]
  apply (ContinuousMap.norm_le (L u) (norm_nonneg u)).mpr
  intro s
  change ‖∫ t in 0..(s : ℝ), pathExtension u t‖ ≤ ‖u‖
  apply (norm_integral_le_of_norm_le_const (fun t _ => u.norm_coe_le_norm _)).trans
  rw [sub_zero, abs_of_nonneg s.property.1]
  exact mul_le_of_le_one_right (norm_nonneg _) s.property.2

omit [CompleteSpace E] in
@[simp] lemma volterra_apply (u : C(unitInterval, E)) (s : unitInterval) :
    volterra u s = ∫ t in 0..(s : ℝ), pathExtension u t := rfl

omit [CompleteSpace E] in
@[simp] lemma volterra_zero (u : C(unitInterval, E)) : volterra u 0 = 0 := by simp

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_FlowParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
universe u v
variable {K : Type v} {E F : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance superpositionMapNorm : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance superpositionMapSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance superpositionContinuousNorm : NormedAddCommGroup C(K, E) := inferInstance
local instance superpositionContinuousSpace : NormedSpace ℝ C(K, E) := inferInstance
local instance superpositionContinuousMapNorm : NormedAddCommGroup C(K, E →L[ℝ] F) := inferInstance
local instance superpositionContinuousMapSpace : NormedSpace ℝ C(K, E →L[ℝ] F) := inferInstance

def continuousMapApply (A : C(K, E →L[ℝ] F)) : C(K, E) →L[ℝ] C(K, F) := by
  let L : C(K, E) →ₗ[ℝ] C(K, F) :=
    { toFun := fun u => ⟨fun x => A x (u x), A.continuous.clm_apply u.continuous⟩
      map_add' := fun u v => by ext x; exact map_add (A x) (u x) (v x)
      map_smul' := fun c u => by ext x; exact map_smul (A x) c (u x) }
  exact L.mkContinuous ‖A‖ (fun u =>
    (ContinuousMap.norm_le (L u) (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
      (fun x => ((A x).le_opNorm (u x)).trans
        (mul_le_mul (A.norm_coe_le_norm x) (u.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _))))

@[simp] lemma continuousMapApply_apply (A : C(K, E →L[ℝ] F)) (u : C(K, E)) (x : K) :
    continuousMapApply A u x = A x (u x) := rfl

lemma continuousMapApply_norm_le (A : C(K, E →L[ℝ] F)) :
    ‖continuousMapApply A‖ ≤ ‖A‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) (fun u =>
    (ContinuousMap.norm_le (continuousMapApply A u) (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
      (fun x => ((A x).le_opNorm (u x)).trans
        (mul_le_mul (A.norm_coe_le_norm x) (u.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _))))

def continuousMapApplyCLM : C(K, E →L[ℝ] F) →L[ℝ] (C(K, E) →L[ℝ] C(K, F)) := by
  let L : C(K, E →L[ℝ] F) →ₗ[ℝ] (C(K, E) →L[ℝ] C(K, F)) :=
    { toFun := continuousMapApply
      map_add' := fun A B => by ext u x; rfl
      map_smul' := fun c A => by ext u x; rfl }
  refine LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := C(K, E →L[ℝ] F)) (F := C(K, E) →L[ℝ] C(K, F)) L 1 ?_
  intro A
  change ‖continuousMapApply A‖ ≤ 1 * ‖A‖
  simpa only [one_mul] using continuousMapApply_norm_le A

def superposition (f : E → F) (hf : Continuous f) : C(K, E) → C(K, F) :=
  fun u => ⟨f ∘ u, hf.comp u.continuous⟩

omit [CompactSpace K] [NormedSpace ℝ E] [NormedSpace ℝ F] in
@[simp] lemma superposition_apply (f : E → F) (hf : Continuous f) (u : C(K, E)) (x : K) :
    superposition f hf u x = f (u x) := rfl


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open Set Filter Function Metric
open scoped Topology ContDiff
universe u


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContDiffSmoothFiniteWave
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance normalFamilyVecNorm : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance normalFamilyVecSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance normalFamilyBiVecNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance normalFamilyBiVecSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance normalFamilyDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance normalFamilyDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_NodalMeasure_ExtrusionEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
namespace YauCounterexamples

def gaussianPairSignProduct (p : ℝ × ℝ × ℝ) (x : Fin 2 → ℝ) : ℝ :=
  (p.2.1 + x 0) * (p.2.2 + p.1 * x 0 + Real.sqrt (1 - p.1 ^ 2) * x 1)

def gaussianPairOppositeProbability (p : ℝ × ℝ × ℝ) : ℝ≥0∞ :=
  (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) {x | gaussianPairSignProduct p x < 0}

end YauCounterexamples

end

open Set Function MeasureTheory
open scoped ENNReal
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_FiniteWaveAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def finiteWaveAmplitude (V : ℕ → E → ℂ) (J : ℕ) (n : ℝ) (x : E) : ℂ :=
  ∑ j ∈ Finset.range (J+1), ((n : ℂ)⁻¹)^j*V j x

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ComplexPolarWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

def leadingComplexJet (z : Fin 3 → ℂ) : (Fin 1 ⊕ Fin 3) → ℂ :=
  Sum.elim (fun _ => 1) z

def selectedComplexJetMatrix (J : Fin 3 → (Fin 1 ⊕ Fin 3) → ℂ) :
    Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ :=
  Matrix.of (fun i j => Sum.elim (fun _ => (J 0 i).re)
    (fun k => ![(J 2 i).re,(J 0 i).im,(J 1 i).im] k) j)


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology ENNReal Matrix.Norms.Elementwise


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_GeneratedCutoffWaveEndpointRatio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal RealInnerProductSpace

variable {I : Type*} [Fintype I]

def rotatedWaveValues (z : I → ℂ) (θ : I → ℝ) : I → ℂ :=
  fun i => Complex.exp ((θ i : ℂ)*Complex.I)*z i

end



open Set Filter
open scoped Topology ContDiff


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_UnitCorrelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped RealInnerProductSpace
namespace YauCounterexamples

section Correlations
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def unitCorrelation (a b : E) : ℝ := ⟪‖a‖⁻¹ • a, ‖b‖⁻¹ • b⟫

end Correlations

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ComplexGaussianRealValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

def selectedCoefficientOrder : (Fin 3 ⊕ Fin 3) ≃ (Fin 2 ⊕ (Fin 1 ⊕ Fin 3)) where
  toFun := Sum.elim
    (fun i => ![Sum.inr (Sum.inl 0),Sum.inl 0,Sum.inr (Sum.inr 0)] i)
    (fun i => ![Sum.inr (Sum.inr 1),Sum.inr (Sum.inr 2),Sum.inl 1] i)
  invFun := Sum.elim
    (fun i => ![Sum.inl 1,Sum.inr 2] i)
    (Sum.elim (fun _ => Sum.inl 0) (fun i => ![Sum.inl 2,Sum.inr 0,Sum.inr 1] i))
  left_inv := by intro i; rcases i with i|i <;> fin_cases i <;> rfl
  right_inv := by
    intro i; rcases i with i|i
    · fin_cases i <;> rfl
    · rcases i with i|i <;> fin_cases i <;> rfl

def selectedComplexCoefficients (v : (Fin 2 → ℝ) × ((Fin 1 ⊕ Fin 3) → ℝ)) : Fin 3 → ℂ :=
  ![(v.2 (.inl 0) : ℂ)-(v.2 (.inr 1) : ℂ)*Complex.I,
    (v.1 0 : ℂ)-(v.2 (.inr 2) : ℂ)*Complex.I,
    (v.2 (.inr 0) : ℂ)-(v.1 1 : ℂ)*Complex.I]


end


open Set MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_GridPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
namespace YauCounterexamples

def gridPoint (d m : ℕ) (δ : ℝ) (k : Fin d → Fin (2 * m + 1)) : Fin d → ℝ :=
  fun j => δ * ((k j : ℕ) - (m : ℝ))

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_CoordinateMetricFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace YauCounterexamples
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def pullbackMetricMatrix (b c : Module.Basis ι ℝ E) (G : E → Matrix ι ι ℝ)
    (f : E → E) (x : E) : Matrix ι ι ℝ :=
  (mixed_jacobianMatrix b c f x).transpose * G (f x) * mixed_jacobianMatrix b c f x

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_CoordinateMetricFirstCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace YauCounterexamples
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def coordinateMetricFirstCoefficient (b : Module.Basis ι ℝ E)
    (G : E → Matrix ι ι ℝ) (x : E) (j : ι) : ℝ :=
  (Real.sqrt (G x).det)⁻¹ * ∑ i, fderiv ℝ (fun y => Real.sqrt (G y).det * (G y)⁻¹ i j) x (b i)

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_PlanePairMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter
open scoped Topology InnerProductSpace
namespace YauCounterexamples
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def planePairMap (a b : V) : (ℝ × ℝ) →ₗ[ℝ] V where
  toFun c := c.1 • a + c.2 • b
  map_add' c d := by simp [add_smul]; abel
  map_smul' r c := by simp [smul_add, smul_smul]

def tangentProjection (p : V) : V →ₗ[ℝ] V :=
  LinearMap.id - (innerSL ℝ p).toLinearMap.smulRight p

@[simp] lemma tangentProjection_apply (p v : V) :
    tangentProjection p v = v - inner ℝ p v • p := rfl

@[simp] lemma planePairMap_apply (a b : V) (s t : ℝ) :
    planePairMap a b (s,t) = s • a + t • b := rfl

def projectedPlaneMap (p a b : V) : (ℝ × ℝ) →ₗ[ℝ] V :=
  (tangentProjection p).comp (planePairMap a b)

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LinearPowerDirectional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def roundChart (p : E) (L : F →ₗᵢ[ℝ] E) (x : F) : E := stereoInvFunAux (-p) (L x)


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function
open scoped ContDiff InnerProductSpace Topology




end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_SphereProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Module Manifold
open scoped Topology ContDiff InnerProductSpace Matrix
variable {n : ℕ}
local instance instFactEqNatFinrankRealEuclideanHAddOfNat_1 : Fact (Module.finrank ℝ (Euclidean (n+1)) = n+1) := ⟨by simp [Euclidean]⟩

def sphereProjection (p : Sphere n) (a : Euclidean (n+1)) : Euclidean (n+1) :=
  a - inner ℝ (p : Euclidean (n+1)) a • (p : Euclidean (n+1))

lemma sphereProjection_orthogonal (p : Sphere n) (a : Euclidean (n+1)) :
    sphereProjection p a ∈ (ℝ ∙ (-(p : Euclidean (n+1))))ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
  simp [sphereProjection,inner_sub_left,inner_smul_left,real_inner_comm a (p : Euclidean (n+1))]

def sphereCoordinates (p : Sphere n) (a : Euclidean (n+1)) : Euclidean n :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere (-p))).repr
    ⟨sphereProjection p a,sphereProjection_orthogonal p a⟩



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_RadialBaseEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set
namespace YauCounterexamples

def radialBaseEnvelope (t r : ℝ) : ℝ := Real.log t+r^2-t^2

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_NormIteratedFDerivCompLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

def realWaveJet (n W : ℝ) (u : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) :
    (Fin 1 ⊕ Fin 3) → ℝ :=
  Sum.elim (fun _ => W⁻¹*u x)
    (fun i => n⁻¹*W⁻¹*fderiv ℝ u x (Pi.single i 1))

end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

def finiteWaveSuperposition {E I : Type*} [Fintype I]
    (w : E → ℝ) (U : I → Fin 3 → E → ℂ) (γ : I → Fin 3 → ℂ) (x : E) : ℝ :=
  w x+∑ i, ∑ ℓ, (γ i ℓ*U i ℓ x).re

end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
open Set
open scoped ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_NormalChartWave
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def smoothChartPush (e : OpenPartialHomeomorph E F) (f : E → V) : F → V :=
  e.target.indicator (f ∘ e.symm)

end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_NormalInverseVecNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance normalInverseVecNorm : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance normalInverseVecSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_FamilyInverseFst
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples
section FiberInverse
variable {P E : Type*} [TopologicalSpace P] [TopologicalSpace E]
variable (e : OpenPartialHomeomorph (P × E) (P × E))
    (he : ∀ w, (e w).1 = w.1)

include he in
lemma familyInverse_fst {w : P × E} (hw : w ∈ e.target) :
    (e.symm w).1 = w.1 := by
  have h := he (e.symm w)
  rw [e.right_inv hw] at h
  exact h.symm

def fiberOpenPartialHomeomorph (q : P) : OpenPartialHomeomorph E E where
  toFun x := (e (q,x)).2
  invFun y := (e.symm (q,y)).2
  source := {x | (q,x) ∈ e.source}
  target := {y | (q,y) ∈ e.target}
  map_source' x hx := by
    have h := e.map_source hx
    have hw : e (q,x) = (q,(e (q,x)).2) := Prod.ext (he _) rfl
    rwa [hw] at h
  map_target' y hy := by
    have h := e.map_target hy
    have hw : e.symm (q,y) = (q,(e.symm (q,y)).2) :=
      Prod.ext (familyInverse_fst e he hy) rfl
    rwa [hw] at h
  left_inv' x hx := by
    have h := congrArg Prod.snd (e.left_inv hx)
    have hw : e (q,x) = (q,(e (q,x)).2) := Prod.ext (he _) rfl
    rwa [hw] at h
  right_inv' y hy := by
    have h := congrArg Prod.snd (e.right_inv hy)
    have hw : e.symm (q,y) = (q,(e.symm (q,y)).2) :=
      Prod.ext (familyInverse_fst e he hy) rfl
    rwa [hw] at h
  open_source := e.open_source.preimage (continuous_const.prodMk continuous_id)
  open_target := e.open_target.preimage (continuous_const.prodMk continuous_id)
  continuousOn_toFun := continuous_snd.continuousOn.comp
    (e.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hx => hx)) (fun _ _ => mem_univ _)
  continuousOn_invFun := continuous_snd.continuousOn.comp
    (e.symm.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hx => hx)) (fun _ _ => mem_univ _)
end FiberInverse

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_LocalizedPacketSignProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal RealInnerProductSpace
section NearFarVectors
variable {I : Type} [Fintype I] [DecidableEq I]

def maskComplex (s : Finset I) (v : I → ℂ) : I → ℂ := fun i => if i ∈ s then v i else 0

end NearFarVectors

end



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal RealInnerProductSpace

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_MiddleBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory BoxIntegral
open scoped Topology
namespace YauCounterexamples

def middleBox (I : Box (Fin 3)) : Box (Fin 3) where
  lower i := (3*I.lower i+I.upper i)/4
  upper i := (I.lower i+3*I.upper i)/4
  lower_lt_upper i := by linarith [I.lower_lt_upper i]

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContDiffPartialIteratedFDeriv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def rescaledCoefficient (f χ : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (p : E) (r : ℝ) : 𝓢(E, ℂ) :=
  (hχc.mul_right (f' := fun x => f (p + r • x) - f p)).toSchwartzMap
    (hχ.mul ((hf.comp (contDiff_const.add (contDiff_const.smul contDiff_id))).sub contDiff_const))

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RescaledDifferentialPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def scaledLowerCoefficient (k : ℕ) (f χ : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (p : E) (r : ℝ) : 𝓢(E, ℂ) :=
  (hχc.mul_right (f' := fun x => (r : ℂ) ^ k * f (p + r • x))).toSchwartzMap
    (hχ.mul (contDiff_const.mul
      (hf.comp (contDiff_const.add (contDiff_const.smul contDiff_id)))))

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
open Matrix ContinuousLinearMap
open scoped InnerProductSpace
open FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Real
open scoped SchwartzMap




end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ConformalMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
namespace YauCounterexamples
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

def weightedLaplacian (g : SmoothMetric E M) (b u : M → ℝ) (x : M) : ℝ :=
  let c := chartAt E x
  let a := metricCoefficients g x
  let ρ := fun y => Real.sqrt (Matrix.det (a y))
  (ρ (c x))⁻¹ * ∑ i, fderiv ℝ
    (fun y => b (c.symm y) * (ρ y * ∑ j, (a y)⁻¹ i j *
      fderiv ℝ (u ∘ c.symm) y (Module.finBasis ℝ E j)))
    (c x) (Module.finBasis ℝ E i)

end YauCounterexamples


end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LocalIntegrationParts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

def realChartLocalize (p : M) (u : M → ℝ) (y : E) : ℝ := by
  classical
  exact if y ∈ (chartAt E p).target then u ((chartAt E p).symm y) else 0


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_RealMatrixCauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
namespace YauCounterexamples
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma real_matrix_cauchy {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (v w : ι → ℝ) :
    (v ⬝ᵥ (A *ᵥ w)) ^ 2 ≤ (v ⬝ᵥ (A *ᵥ v)) * (w ⬝ᵥ (A *ᵥ w)) := by
  have hs : Aᵀ = A := Matrix.isHermitian_iff_isSymm.mp hA.isHermitian
  have he : w ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ w) := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs]
  have hp (t : ℝ) : 0 ≤ (v ⬝ᵥ (A *ᵥ v)) * (t * t) +
      (2 * (v ⬝ᵥ (A *ᵥ w))) * t + (w ⬝ᵥ (A *ᵥ w)) := by
    have h := hA.dotProduct_mulVec_nonneg (t • v + w)
    simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_smul,
      add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul] at h
    rw [he] at h
    nlinarith [h]
  have h := discrim_le_zero hp
  dsimp [discrim] at h
  nlinarith

lemma real_dual_matrix_cauchy {A : Matrix ι ι ℝ} (hA : A.PosDef) (p z : ι → ℝ) :
    (p ⬝ᵥ z) ^ 2 ≤ (p ⬝ᵥ (A⁻¹ *ᵥ p)) * (z ⬝ᵥ (A *ᵥ z)) := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  have hc : A *ᵥ (A⁻¹ *ᵥ p) = p := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  have hs : Aᵀ = A := Matrix.isHermitian_iff_isSymm.mp hA.isHermitian
  have he : (A⁻¹ *ᵥ p) ⬝ᵥ (A *ᵥ z) = p ⬝ᵥ z := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs, hc]
  have h := real_matrix_cauchy hA.posSemidef (A⁻¹ *ᵥ p) z
  rw [hc, he, dotProduct_comm (A⁻¹ *ᵥ p) p] at h
  exact h

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_NormIteratedFDerivScalarDirection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

def coordinateDivergence (e : ι → E) (ρ : E → ℝ) (X : ι → E → ℝ) (x : E) : ℝ :=
  (ρ x)⁻¹ * ∑ i, fderiv ℝ (fun y => ρ y * X i y) x (e i)

def scalarCorrectionDenominator (e : ι → E) (n : ℝ) (U : E → ℝ)
    (X : ι → E → ℝ) (x : E) : ℝ :=
  n ^ 2 * U x ^ 2 + ∑ i, fderiv ℝ U x (e i) * X i x

def scalarCorrectionRatio (e : ι → E) (ρ : E → ℝ) (n Λ : ℝ) (U : E → ℝ)
    (X : ι → E → ℝ) (x : E) : ℝ :=
  (coordinateDivergence e ρ X x + Λ * U x) / scalarCorrectionDenominator e n U X x

def scalarCorrectionB (e : ι → E) (ρ : E → ℝ) (n Λ : ℝ) (U : E → ℝ)
    (X : ι → E → ℝ) (x : E) : ℝ :=
  1 - scalarCorrectionRatio e ρ n Λ U X x * U x

def scalarCorrectionS (e : ι → E) (ρ : E → ℝ) (n Λ : ℝ) (U : E → ℝ)
    (X : ι → E → ℝ) (x : E) : ℝ :=
  1 - Λ⁻¹ * (n ^ 2 * scalarCorrectionRatio e ρ n Λ U X x * U x -
    coordinateDivergence e ρ (fun i y => scalarCorrectionRatio e ρ n Λ U X y * X i y) x)


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ScalarCompDirectional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

def coordinateGradientPair (g : SmoothMetric E M) (u v : M → ℝ) (x : M) : ℝ :=
  ∑ i, ∑ j, (metricCoefficients g x ((chartAt E x) x))⁻¹ i j *
    fderiv ℝ (u ∘ (chartAt E x).symm) ((chartAt E x) x) (Module.finBasis ℝ E i) *
    fderiv ℝ (v ∘ (chartAt E x).symm) ((chartAt E x) x) (Module.finBasis ℝ E j)


end

open Set Filter Manifold
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_RoundMetricExists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

def scalarDifferential (u : M → ℝ) (x : M) : TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ :=
  mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x

lemma scalarDifferential_coordinateVector {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target) (i : CoordIndex E) :
    scalarDifferential u ((chartAt E p).symm y) (coordinateVector p y i) =
      fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E i) := by
  have hc : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm y :=
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy
      (n := ∞)).mdifferentiableAt (by simp)
  have he := mfderiv_comp y (hu.mdifferentiable (by simp) _) hc
  rw [mfderiv_eq_fderiv] at he
  exact (congrArg (fun T => T (Module.finBasis ℝ E i)) he).symm

lemma rankOne_coercive (a b F G D : ℝ) (hG : 0 ≤ G) (hD : D ^ 2 ≤ F * G) :
    min a (a + b * F) * G ≤ a * G + b * D ^ 2 := by
  by_cases hb : 0 ≤ b
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hG).trans
      (le_add_of_nonneg_right (mul_nonneg hb (sq_nonneg D)))
  · have hb' : b ≤ 0 := le_of_not_ge hb
    have h := mul_le_mul_of_nonpos_left hD hb'
    have hm := mul_le_mul_of_nonneg_right (min_le_right a (a + b * F)) hG
    nlinarith


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_PinnedMetricJointGradientPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

lemma contMDiffAt_exp_along {f : D → M}
    (K : ∀ z, TangentSpace 𝓘(ℝ,E) (f z) →L[ℝ] TangentSpace 𝓘(ℝ,E) (f z)) {z₀ : D}
    (hk : ContMDiffAt 𝓘(ℝ,D) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun z => (⟨f z, K z⟩ : TotalSpace (E →L[ℝ] E)
        (fun x : M => TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x))) z₀) :
    ContMDiffAt 𝓘(ℝ,D) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun z => (⟨f z, (show E →L[ℝ] E from NormedSpace.exp (show E →L[ℝ] E from K z))⟩ :
        TotalSpace (E →L[ℝ] E) (fun x : M => TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x))) z₀ := by
  have he : ContDiff ℝ ∞ (NormedSpace.exp : (E →L[ℝ] E) → (E →L[ℝ] E)) :=
    (show AnalyticOnNhd ℝ NormedSpace.exp Set.univ from
      fun x _ => NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiff
  rw [contMDiffAt_totalSpace] at hk ⊢
  refine ⟨hk.1, ?_⟩
  have hh := he.contMDiff.contMDiffAt.comp z₀ hk.2
  apply hh.congr_of_eventuallyEq
  have hn := (trivializationAt E (TangentSpace 𝓘(ℝ,E)) (f z₀)).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E _ (f z₀))
  filter_upwards [hk.1.continuousAt.preimage_mem_nhds hn] with z hz
  change f z ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) (f z₀)).baseSet at hz
  simp only [Function.comp_def,hom_trivializationAt_apply]
  let : NormedAlgebra ℚ (E →L[ℝ] E) := .restrictScalars ℚ ℝ (E →L[ℝ] E)
  let e : E ≃L[ℝ] E :=
    (trivializationAt E (TangentSpace 𝓘(ℝ,E)) (f z₀)).continuousLinearEquivAt ℝ (f z) hz
  have hm := NormedSpace.map_exp e.conjContinuousAlgEquiv
    (e.arrowCongr e).continuous (show E →L[ℝ] E from K z)
  erw [ContinuousLinearMap.inCoordinates_eq hz hz,
    ContinuousLinearMap.inCoordinates_eq hz hz]
  convert hm using 1 <;> rfl

end


open Set Filter Function Manifold Bundle MeasureTheory
open scoped Topology ContDiff Matrix BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_PrepDualNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open Set Filter Function Metric
open scoped Topology ContDiff
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
namespace YauCounterexamples
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance prepDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance prepDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_GlobalPrepDualNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
section
open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples
open Set Filter Function
open scoped Topology ContDiff
variable {E V F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def preparationCorrugation (ψ χ : E → ℝ) (F₀ : V → ℝ) (y : E → V)
    (d N : ℝ) (τ : V) (x : E) : ℝ :=
  ψ x+(d/N/N)*(χ x*F₀ (N • y x+τ))

end YauCounterexamples

end

open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples

def preparationWave (t : ℝ) : ℝ := -Real.cos (2*Real.pi*t)/(2*Real.pi^2)

def preparationWaveFirst (t : ℝ) : ℝ := Real.sin (2*Real.pi*t)/Real.pi

def preparationWaveSecond (t : ℝ) : ℝ := 2*Real.cos (2*Real.pi*t)

end YauCounterexamples

end


namespace YauCounterexamples
noncomputable section
open Set Filter Function Metric Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance globalPrepDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance globalPrepDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

end
end YauCounterexamples

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContinuousCompactSmoothJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
local instance mcfMapMatrixNorm {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedAddCommGroup (E →L[ℝ] Matrix ι κ ℝ) :=
  inferInstanceAs (NormedAddCommGroup (E →L[ℝ] (ι → κ → ℝ)))


end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance hmsDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance


end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {n : ℕ}
local instance spnENorm : NormedAddCommGroup (Euclidean n) := inferInstance
local instance spnESpace : NormedSpace ℝ (Euclidean n) := inferInstance
local instance spnDualNorm : NormedAddCommGroup (Euclidean n →L[ℝ] ℝ) := inferInstance
local instance spnDualSpace : NormedSpace ℝ (Euclidean n →L[ℝ] ℝ) := inferInstance


end

section
open Set Filter Manifold
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E]
local instance matrixJetInst1 : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance matrixJetInst2 : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
end


open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction Matrix.Norms.Elementwise

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SmDualNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open Set Filter Function Metric
open scoped Topology ContDiff
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance jetDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance jetDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance


end

open Set Filter Metric
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance smDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance smDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_OscDualNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace YauCounterexamples
noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance oscDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

end
end YauCounterexamples

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_RadialFiniteDualNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace YauCounterexamples
noncomputable section
section
open Set Filter Function Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff InnerProductSpace ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance radialShiftMetricDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance radialShiftMetricDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
end


open Set Function Filter Metric MeasureTheory Manifold Bundle
open scoped Topology ENNReal InnerProductSpace ContDiff

end
end YauCounterexamples

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_UnitSphereProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace
variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [FiniteDimensional ℝ A] {n : ℕ} [Fact (Module.finrank ℝ A = n+1)]
omit [FiniteDimensional ℝ A]
def unitSphereFrame (p : Metric.sphere (0 : A) 1) : Euclidean n →ₗᵢ[ℝ] A :=
  (ℝ ∙ (-(p : A)))ᗮ.subtypeₗᵢ.comp
    (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere (-p))).repr.symm.toLinearIsometry

end


open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace
variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [FiniteDimensional ℝ A] {n : ℕ} [Fact (Module.finrank ℝ A = n+1)]
omit [FiniteDimensional ℝ A]
def unitSphereProjection (p : Metric.sphere (0 : A) 1) (a : A) : A :=
  a - inner ℝ (p : A) a • (p : A)

lemma unitSphereProjection_orthogonal (p : Metric.sphere (0 : A) 1) (a : A) :
    unitSphereProjection p a ∈ (ℝ ∙ (-(p : A)))ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
  simp [unitSphereProjection,inner_sub_left,inner_smul_left,real_inner_comm a (p : A)]

def unitSphereCoordinates (p : Metric.sphere (0 : A) 1) (a : A) : Euclidean n :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere (-p))).repr
    ⟨unitSphereProjection p a,unitSphereProjection_orthogonal p a⟩


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ProductSphereFstPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
variable {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ B]
  {n m : ℕ} [Fact (Module.finrank ℝ A = n+1)] [Fact (Module.finrank ℝ B = m+1)]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def productSphere_fstPower (p : Metric.sphere (0:A) 1) (ℓ : A →L[ℝ] ℂ) (k : ℕ) :
    WithLp 2 (Euclidean n×Euclidean m) → ℂ :=
  (fun y => (ℓ (roundChart (p:A) (unitSphereFrame (n:=n) p) y))^k) ∘
    WithLp.fstL 2 ℝ (Euclidean n) (Euclidean m)

def productSphere_sndPower (p : Metric.sphere (0:B) 1) (ℓ : B →L[ℝ] ℂ) (k : ℕ) :
    WithLp 2 (Euclidean n×Euclidean m) → ℂ :=
  (fun y => (ℓ (roundChart (p:B) (unitSphereFrame (n:=m) p) y))^k) ∘
    WithLp.sndL 2 ℝ (Euclidean n) (Euclidean m)
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_ScalarCauchyCross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

def cutoffFactor (χ v : M → ℝ) (x : M) : ℝ := 1+χ x*(v x-1)

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LpProductLinearMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples
section LpProductJets
variable {E F A B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
def lpProductLinearMap (f : E →L[ℝ] A) (g : F →L[ℝ] B) :
    WithLp 2 (E×F) →L[ℝ] WithLp 2 (A×B) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ A B).symm.toContinuousLinearMap.comp
    ((f.prodMap g).comp (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toContinuousLinearMap)
@[simp] lemma lpProductLinearMap_apply (f : E →L[ℝ] A) (g : F →L[ℝ] B)
    (x : WithLp 2 (E×F)) :
    lpProductLinearMap f g x = WithLp.toLp 2 (f x.fst,g x.snd) := rfl

def lpProductFunction (f : E → A) (g : F → B) (x : WithLp 2 (E×F)) :
    WithLp 2 (A×B) := WithLp.toLp 2 (f x.fst,g x.snd)
end LpProductJets
variable {E F A B : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
def lpProductIsometry (f : E →ₗᵢ[ℝ] A) (g : F →ₗᵢ[ℝ] B) :
    WithLp 2 (E×F) →ₗᵢ[ℝ] WithLp 2 (A×B) :=
  (lpProductLinearMap f.toContinuousLinearMap g.toContinuousLinearMap).toLinearMap.isometryOfInner
    (by intro x y; simp [WithLp.prod_inner_apply])
@[simp] lemma lpProductIsometry_apply (f : E →ₗᵢ[ℝ] A) (g : F →ₗᵢ[ℝ] B)
    (x : WithLp 2 (E×F)) : lpProductIsometry f g x = WithLp.toLp 2 (f x.fst,g x.snd) := rfl
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_RoundPowerRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
open Set Filter
open scoped Topology ContDiff ComplexConjugate

def powerRadiusMap (n : ℕ) (z : ℂ) : ℝ × ℝ := ((z^n).re, Complex.normSq z)

end

open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
open Set Filter
open scoped Topology ContDiff ComplexConjugate



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ProductFrequencyTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Filter
open scoped Topology

def sphereFrequency (n : ℕ) : ℝ := (n : ℝ) * (n + 2)
def inverseFrequency (n : ℕ) : ℝ := (n : ℝ)⁻¹

end

section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
local instance sphereN_dimension_fact (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1)) = n+1) := ⟨by simp [Euclidean]⟩


def productFrequency (k : ℕ) : ℝ := 2*(k:ℝ)^2+(k:ℝ)
end


section
open Set Filter
open scoped Topology

def productWaveFrequency (k : ℕ) : ℝ := Real.sqrt (productFrequency k+1)-1
end


open Set Filter Function Manifold
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ThreeFirstNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
local instance sphereFirst_dimension_fact (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1))=n+1) := ⟨by simp [Euclidean]⟩
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ThreeCoupledNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
local instance threeCoupled_dimension_fact (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1))=n+1) := ⟨by simp [Euclidean]⟩
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ThreeDirectionsNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
local instance threeDirections_dimension_fact (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1))=n+1) := ⟨by simp [Euclidean]⟩
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_ExistsCompactSignedEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local instance perturbDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance perturbDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
end


open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeFormulaNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
local instance threeFormula_dimension_fact (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1))=n+1) := ⟨by simp [Euclidean]⟩
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeRobustProfileNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace

def threeEnvelopeExponent : ℝ := (Real.sqrt 2)⁻¹
end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace

def threeCouplingRadius : ℝ := 1/100
end


open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_SphericalFixedFormNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

def sphericalStageRadius (n : ℕ) : ℝ := 3/10-1/(10*((n:ℝ)+1))

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_NodalMeasure_SphericalNodalFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
section IntrinsicForwardLipschitz
variable {E M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) 1 M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

local instance intrinsicForwardMapNorm (x : M) (y : F) :
    NormedAddCommGroup (TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,F) y) :=
  inferInstanceAs (NormedAddCommGroup (TangentSpace 𝓘(ℝ,E) x →L[ℝ] F))

end IntrinsicForwardLipschitz
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace


end


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral MeasureTheory
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_FourLiftThreeSmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


open Set Filter Manifold Bundle Function
open scoped Topology ContDiff
local instance fourLiftRealSmul : ContinuousSMul ℝ ℝ := IsBoundedSMul.continuousSMul

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_ProductMetric_FourWaveThreeSmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


open Set Filter Manifold Bundle Function Matrix BoxIntegral MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise ENNReal NNReal
local instance fourWaveCircleSmul : ContinuousSMul ℝ (Euclidean 1) := IsBoundedSMul.continuousSMul
def fourTailHeadLinear : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) × ℝ where
  toFun x := (Fin.tail x,x 0)
  invFun x := Fin.cons x.2 x.1
  left_inv x := by ext i; exact Fin.cases rfl (fun j => rfl) i
  right_inv x := by rfl
  map_add' x y := rfl
  map_smul' t x := rfl
def fourTailHeadEquiv : (Fin 4 → ℝ) ≃L[ℝ] (Fin 3 → ℝ) × ℝ := fourTailHeadLinear.toContinuousLinearEquiv
def fourCircleCoord : ℝ ≃L[ℝ] Euclidean 1 := ContinuousLinearEquiv.ofFinrankEq (by simp [Euclidean])

end YauCounterexamples
end

end OAI
end


