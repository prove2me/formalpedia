-- Prove2me | Definitions.Def_OAIQ036S001
-- name    : OAIQ036S001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T04:46:19.749128+00:00
-- url     : https://prove2.me/theorems/1dbd4453-f9d7-4703-9509-6942136dba17
-- title:
--   Definitions bundle OAIQ036S001 of the split of OpenAI, Stretched-exponential barriers for typical SK initial states
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SK.main`, carved from OpenAI's openai/math development (OpenAI, *Stretched-exponential barriers for typical SK initial states*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 277 declarations of OpenAI's Lean: 183 definitions, 7 instances and 87 theorems. The definitions and types are `OAI.SK.Analytic.TranslationInvariant`, `OAI.SK.Analytic.TripleRetainedState`, `OAI.SK.Analytic.admissibleQuantiles`, `OAI.SK.Analytic.affineGibbs`, `OAI.SK.Analytic.affineLogPartition`, `OAI.SK.Analytic.affineMoment`, `OAI.SK.Analytic.appendTimeGrid`, `OAI.SK.Analytic.bankEndpointError`, `OAI.SK.Analytic.bankPrefix`, `OAI.SK.Analytic.blockAtom`, `OAI.SK.Analytic.blockCoefficients`, `OAI.SK.Analytic.blockDimension`, `OAI.SK.Analytic.blockInteraction`, `OAI.SK.Analytic.blockInterpolationChoice`, `OAI.SK.Analytic.blockLevel`, `OAI.SK.Analytic.blockMass`, `OAI.SK.Analytic.blockObservable`, `OAI.SK.Analytic.blockPrior`, `OAI.SK.Analytic.blockSiteEmbedding`, `OAI.SK.Analytic.blockSiteOwner`, `OAI.SK.Analytic.boundedPrimitive`, `OAI.SK.Analytic.cdfDistance`, `OAI.SK.Analytic.cdfMassSegment`, `OAI.SK.Analytic.cdfMassSegmentStieltjes`, `OAI.SK.Analytic.chainSum`, `OAI.SK.Analytic.clampQuantile`, `OAI.SK.Analytic.clockWeight`, `OAI.SK.Analytic.codeOverlap`, `OAI.SK.Analytic.commonBranchEmbedding`, `OAI.SK.Analytic.conditionalSusceptibilityLipschitz`, `OAI.SK.Analytic.conditionalWeights`, `OAI.SK.Analytic.covarianceMatrix`, `OAI.SK.Analytic.coverageAngle`, `OAI.SK.Analytic.coverageGainRate`, `OAI.SK.Analytic.coveragePrefix`, `OAI.SK.Analytic.crossCovarianceMatrix`, `OAI.SK.Analytic.cumulativeGapMap`, `OAI.SK.Analytic.directionalGradient`, `OAI.SK.Analytic.dyadicCDFDistance`, `OAI.SK.Analytic.dyadicIntervals` and 143 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability/SKBarriers, in whole or in part: `SKBarriers_Calculus_BrascampLieb`, `SKBarriers_Calculus_CoordinateSigns`, `SKBarriers_Calculus_MarginalPotential`, `SKBarriers_Coverage_CoverageAngle`, `SKBarriers_Coverage_CoverageGainRate`, `SKBarriers_Coverage_CoverageSchedule`, `SKBarriers_Coverage_FiniteCoverage`, `SKBarriers_Coverage_FiniteRate`, `SKBarriers_Coverage_ThermodynamicLimit`, `SKBarriers_Coverage_UniformCoverage`, `SKBarriers_Dynamics_BankCardinality`, `SKBarriers_Dynamics_BankNumerics`, `SKBarriers_Dynamics_BankPool`, `SKBarriers_Dynamics_Crossing`, `SKBarriers_Dynamics_ForbiddenMain`, `SKBarriers_Dynamics_GreedyNumerics`, `SKBarriers_Dynamics_GridThreshold`, `SKBarriers_Dynamics_HeatBathChoice`, `SKBarriers_Dynamics_IdentityDynamics`, `SKBarriers_Dynamics_PredictableGrid`, `SKBarriers_Dynamics_Uniformization`, `SKBarriers_Gaussian_BlockStein`, `SKBarriers_Gaussian_BoundedPrimitive`, `SKBarriers_Gaussian_GaussianAngle`, `SKBarriers_Gaussian_GaussianAverage`, `SKBarriers_Gaussian_GaussianCovarianceStep`, `SKBarriers_Gaussian_GaussianMassDerivative`, `SKBarriers_Gaussian_GaussianMassStability`, `SKBarriers_Gaussian_GaussianResponse`, `SKBarriers_Gaussian_GaussianRotation`, `SKBarriers_Gaussian_GaussianSpinTrace`, `SKBarriers_Gaussian_SmoothObservables`, `SKBarriers_Gaussian_SmoothedObservable`, `SKBarriers_Hierarchy_AppendTimeGrid`, `SKBarriers_Hierarchy_AverageMeanVariance`, `SKBarriers_Hierarchy_BlockObservable`, `SKBarriers_Hierarchy_BlockSiteEmbedding`, `SKBarriers_Hierarchy_BlockSiteFields`, `SKBarriers_Hierarchy_HierarchyLevels`, `SKBarriers_Hierarchy_HierarchyMassPrefix`, `SKBarriers_Hierarchy_RootSusceptibility`, `SKBarriers_Hierarchy_WeightedBlockMass`, `SKBarriers_Hierarchy_WeightedListBridge`, `SKBarriers_Interpolation_AdaptiveODERegular`, `SKBarriers_Interpolation_FiniteCovarianceComparison`, `SKBarriers_Interpolation_FiniteCovarianceInterpolation`, `SKBarriers_Interpolation_SKBlockCoordinates`, `SKBarriers_Locking_FourBlockMass`, `SKBarriers_Locking_NarrowClockAlgebra`, `SKBarriers_Locking_NarrowCoefficientBound`, `SKBarriers_Locking_NarrowScaleAlgebra`, `SKBarriers_Locking_NarrowSchedule`, `SKBarriers_Locking_NarrowTimeQuadratic`, `SKBarriers_Parisi_CDFHeatPrefix`, `SKBarriers_Parisi_CDFJointLoss`, `SKBarriers_Parisi_CDFJointSusceptibility`, `SKBarriers_Parisi_CDFMassSegment`, `SKBarriers_Parisi_CDFOptimality`, `SKBarriers_Parisi_CDFOverlap`, `SKBarriers_Parisi_CDFOverlapConvergence`, `SKBarriers_Parisi_CDFPartitionRepresentation`, `SKBarriers_Parisi_CDFQuantileInverse`, `SKBarriers_Parisi_CDFUniformQuantiles`, `SKBarriers_Parisi_QuantileCDFOverlap`, `SKBarriers_Parisi_QuantileChain`, `SKBarriers_Parisi_QuantileClamp`, `SKBarriers_Parisi_QuantileLipschitz`, `SKBarriers_Parisi_QuantileMinimizer`, `SKBarriers_Parisi_QuantileScalarOverlap`, `SKBarriers_Parisi_QuantileTransport`, `SKBarriers_Parisi_QuantileWeakCompactness`, `SKBarriers_Replicas_CommonBranch`, `SKBarriers_Replicas_MatrixChain`, `SKBarriers_Replicas_MatrixCovarianceAlgebra`, `SKBarriers_Replicas_MatrixGuerraEndpoints`, `SKBarriers_Replicas_MatrixGuerraKernel`, `SKBarriers_Replicas_OverlapCode`, `SKBarriers_Replicas_PairBlocks`, `SKBarriers_Replicas_PairFactor`, `SKBarriers_Replicas_ReplicaOverlap`, `SKBarriers_Replicas_TripleCDFTrial`, `SKBarriers_Replicas_TripleClockAlgebra`, `SKBarriers_Replicas_TripleFiniteExpansion`, `SKBarriers_Replicas_TriplePerturbation`, `SKBarriers_Replicas_TripleRetained`, `SKBarriers_Replicas_TripleSchedule`, `SKBarriers_Replicas_TripleScheduleEndpoint`, `SKBarriers_Replicas_TripleTailValue`, `SKBarriers_Replicas_VectorBranch`, `SKBarriers_Scalar_DerivativeStability`, `SKBarriers_Scalar_DslopeLipschitz`, `SKBarriers_Scalar_DyadicCDFStability`, `SKBarriers_Scalar_DyadicScalar`, `SKBarriers_Scalar_DyadicSpin`, `SKBarriers_Scalar_EmbeddedSites`, `SKBarriers_Scalar_PartitionChain`, `SKBarriers_Scalar_PartitionOverlap`, `SKBarriers_Scalar_RankOneMatrix`, `SKBarriers_Scalar_ScalarAtomic`, `SKBarriers_Scalar_ScalarAverageCalculus`, `SKBarriers_Scalar_ScalarEarlyMoment`, `SKBarriers_Scalar_ScalarEndpoint`, `SKBarriers_Scalar_ScalarGeneralTerminal`, `SKBarriers_Scalar_ScalarHessianFloor`, `SKBarriers_Scalar_ScalarInstability`, `SKBarriers_Scalar_ScalarLocalTentMoments`, `SKBarriers_Scalar_ScalarOneAtom`, `SKBarriers_Scalar_ScalarOneAtomMoments`, `SKBarriers_Scalar_ScalarSemigroup`, `SKBarriers_Scalar_ScalarSpinRecursion`, `SKBarriers_Scalar_ScalarSymmetricTaylor`, `SKBarriers_Scalar_ScalarTentGeometry`, `SKBarriers_Scalar_ScalarTiltedExpectation`, `SKBarriers_Scalar_TerminalPathStability`, `SKBarriers_Scalar_TerminalPerturbation`, `SKBarriers_Scalar_ThermalMoments`, `SKBarriers_Scalar_UniformDerivativeLimit`, `SKBarriers_SpinGlass_FinitePartition`, `SKBarriers_SpinGlass_FinitePenalty`, `SKBarriers_SpinGlass_FinitePrefix`, `SKBarriers_SpinGlass_FiniteScalarGap`, `SKBarriers_SpinGlass_GaugeSymmetry`, `SKBarriers_SpinGlass_LogPartition`, `SKBarriers_SpinGlass_SpinParameterMoments`, `SKBarriers_SpinGlass_SpinSiteTensorization`.
--
--   **Imports.** It imports the published bundle `Def_SKBarriers`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ036S002` and `OAIQ036S003`; the statement `OAI.SK.Analytic.stretched_uniform_coverage`.
-- source:
--   OpenAI, Stretched-exponential barriers for typical SK initial states, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/SKBarriers at commit adc7f12

import Mathlib
import Definitions.Def_SKBarriers

section
-- module Solutions.OAIQ036_SK.Compat
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
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_BrascampLieb
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic

def intervalPartition (V : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ x in a..b, Real.exp (-V x)

def intervalMean (V f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (∫ x in a..b, f x * Real.exp (-V x)) / intervalPartition V a b

end SK.Analytic

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_MarginalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic

def marginalPotential {E : Type} (V : E × ℝ → ℝ) (a b : ℝ) (x : E) : ℝ :=
  -Real.log (intervalPartition (fun y => V (x,y)) a b)

end SK.Analytic

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_FinitePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic
section FinitePartition
variable {E S : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype S] [Nonempty S]

def affineLogPartition (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (x : E) : ℝ :=
  Real.log (∑ s, Real.exp (c s+L s x))

end FinitePartition
end SK.Analytic

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_CoordinateSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic

def scalarSign (b : Bool) : ℝ → ℝ := fun x => if b then -x else x

@[simp] theorem scalarSign_involutive (b : Bool) (x : ℝ) :
    scalarSign b (scalarSign b x) = x := by cases b <;> simp [scalarSign]

@[simp] theorem scalarSign_square (b : Bool) (x : ℝ) :
    (scalarSign b x)^2 = x^2 := by cases b <;> simp [scalarSign]

@[simp] theorem scalarSign_false : scalarSign false = id := by
  funext x; simp [scalarSign]

@[simp] theorem scalarSign_true : scalarSign true = fun x : ℝ => -x := by
  funext x; simp [scalarSign]

theorem scalarSign_continuous (b : Bool) : Continuous (scalarSign b) := by
  cases b <;> simp only [scalarSign_false,scalarSign_true] <;> fun_prop

def scalarSignEquiv (b : Bool) : ℝ ≃ᵐ ℝ where
  toFun := scalarSign b
  invFun := scalarSign b
  left_inv := scalarSign_involutive b
  right_inv := scalarSign_involutive b
  measurable_toFun := (scalarSign_continuous b).measurable
  measurable_invFun := (scalarSign_continuous b).measurable

end SK.Analytic

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_CoverageAngle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

def coverageAngle (L : ℕ → ℝ) (M : ℝ) (n : ℕ) : ℝ := Real.sqrt (M*L n/(n:ℝ))

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_LogPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK

def unitIntervalLaw : Measure ℝ := volume.restrict (Set.Ioc 0 1)

instance unitIntervalLaw_probability : IsProbabilityMeasure unitIntervalLaw := by
  constructor
  simp [unitIntervalLaw]

end SK
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic

section Directional
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def directionalGradient (F : E → ℝ) (u : E) (z : E) : ℝ := fderiv ℝ F z u

theorem directionalGradient_contDiff (F : E → ℝ) (hF : ContDiff ℝ 2 F) (u : E) :
    ContDiff ℝ 1 (directionalGradient F u) :=
  (hF.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem fderiv_directionalGradient (F : E → ℝ) (hF : ContDiff ℝ 2 F) (u z : E) :
    fderiv ℝ (directionalGradient F u) z = (fderiv ℝ (fderiv ℝ F) z).flip u := by
  have H := (((hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z).hasFDerivAt.clm_apply
    (hasFDerivAt_const u z)).fderiv
  change fderiv ℝ (fun y => fderiv ℝ F y u) z = _
  simpa only [ContinuousLinearMap.comp_zero,zero_add] using H

end Directional

end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianCovarianceStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
section CovarianceStep
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance instSMulZeroClassRealContinuousLinearMapId_solutions : SMulZeroClass ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  (@Module.toDistribMulAction ℝ (E →L[ℝ] E →L[ℝ] ℝ) inferInstance inferInstance inferInstance).toDistribSMul.toSMulZeroClass

local instance instIsBoundedSMulRealContinuousLinearMapId_solutions : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  @NormedSpace.toIsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) _ _ _

end CovarianceStep
end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
section GaussianAverage
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def prefixGradient (f : E × ℝ → ℝ) (u : E) (z : E × ℝ) : ℝ :=
  fderiv ℝ f z (u,0)

def prefixHessian (f : E × ℝ → ℝ) (u v : E) (z : E × ℝ) : ℝ :=
  fderiv ℝ (fderiv ℝ f) z (u,0) (v,0)

end GaussianAverage
end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic

def hierarchyAtom : (n : ℕ) → (Fin n → ℝ) → ℝ → Fin (n+1) → ℝ
  | 0,_,u,_ => u
  | n+1,m,u,j => Fin.lastCases (u-m (Fin.last n))
      (hierarchyAtom n (fun i => m i.castSucc) (m (Fin.last n))) j

section Translation
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def TranslationInvariant (f : E → ℝ) (u : E) : Prop := ∀ (z : E) (t : ℝ), f (z+t • u) = f z

end Translation

end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_SmoothObservables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic

section SmoothObservables
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def gradientSquareSum {I : Type} [Fintype I] (F : E → ℝ) (u : I → E) (z : E) : ℝ :=
  ∑ i, directionalGradient F (u i) z*directionalGradient F (u i) z

end SmoothObservables

end SK.Analytic

end
end
end
end
end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ThermalMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
section ThermalMoments
variable {E S : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype S] [Nonempty S]

def affineGibbs (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (x : E) (s : S) : ℝ :=
  Real.exp (c s+L s x)/(∑ t, Real.exp (c t+L t x))

def affineMoment (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (g : S → ℝ) (x : E) : ℝ :=
  ∑ s, affineGibbs c L x s*g s

theorem affinePartition_pos (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (x : E) :
    0 < ∑ s, Real.exp (c s+L s x) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

theorem affineGibbs_pos (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (x : E) (s : S) :
    0 < affineGibbs c L x s := div_pos (Real.exp_pos _) (affinePartition_pos c L x)

theorem affineGibbs_sum (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (x : E) :
    ∑ s, affineGibbs c L x s = 1 := by
  simp only [affineGibbs,← Finset.sum_div]
  exact div_self (affinePartition_pos c L x).ne'

theorem affineMoment_continuous (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (g : S → ℝ) :
    Continuous (affineMoment c L g) := by
  apply continuous_finsetSum
  intro s _
  apply Continuous.mul _ continuous_const
  exact (Real.continuous_exp.comp (continuous_const.add (L s).continuous)).div
    (continuous_finsetSum _ (fun i _ => Real.continuous_exp.comp (continuous_const.add (L i).continuous)))
    (fun x => (affinePartition_pos c L x).ne')

theorem affineMoment_norm_le (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (g : S → ℝ)
    {C : ℝ} (hC : ∀ s, ‖g s‖ ≤ C) (x : E) : ‖affineMoment c L g x‖ ≤ C := by
  calc
    ‖affineMoment c L g x‖ ≤ ∑ s, ‖affineGibbs c L x s*g s‖ := norm_sum_le _ _
    _ = ∑ s, affineGibbs c L x s*‖g s‖ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [norm_mul,Real.norm_eq_abs,abs_of_pos (affineGibbs_pos c L x s)]
    _ ≤ ∑ s, affineGibbs c L x s*C :=
      Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hC s) (affineGibbs_pos c L x s).le)
    _ = C := by rw [← Finset.sum_mul,affineGibbs_sum,one_mul]

theorem fderiv_affineLogPartition_apply (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (x u : E) :
    fderiv ℝ (affineLogPartition c L) x u = affineMoment c L (fun s => L s u) x := by
  classical
  let Z : E → ℝ := fun x => ∑ s, Real.exp (c s+L s x)
  have hz (x : E) : HasFDerivAt Z (∑ s, Real.exp (c s+L s x) • L s) x := by
    apply HasFDerivAt.fun_sum
    intro s _
    simpa only [zero_add] using ((hasFDerivAt_const (c s) x).fun_add (L s).hasFDerivAt).exp
  have hp : Z x ≠ 0 := (affinePartition_pos c L x).ne'
  change fderiv ℝ (fun y => Real.log (Z y)) x u = _
  rw [(hz x |>.log hp).fderiv]
  simp only [smul_apply,smul_eq_mul,sum_apply,affineMoment,affineGibbs,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  change (Z x)⁻¹*(Real.exp (c s+L s x)*L s u) = Real.exp (c s+L s x)/(Z x)*L s u
  ring

end ThermalMoments
end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_BlockStein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

def normalizedDot {N : ℕ} (a b : Fin N → ℝ) : ℝ := (∑ i, a i*b i)/(N : ℝ)

def normalizedSquare {N : ℕ} (a : Fin N → ℝ) : ℝ := (∑ i, (a i)^2)/(N : ℝ)

theorem normalizedSquare_nonneg {N : ℕ} (a : Fin N → ℝ) : 0 ≤ normalizedSquare a := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)

theorem normalizedSquare_le_one {N : ℕ} (a : Fin N → ℝ) (ha : ∀ i, |a i| ≤ 1) :
    normalizedSquare a ≤ 1 := by
  by_cases hN : N = 0
  · simp [normalizedSquare,hN]
  have hn : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  apply (div_le_iff₀ hn).2
  calc
    (∑ i, (a i)^2) ≤ ∑ _ : Fin N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [ha i,sq_abs (a i),abs_nonneg (a i)]
    _ = 1*(N : ℝ) := by simp

end SK.Analytic
namespace SK.Analytic

def massFromAtoms (n : ℕ) (w : Fin (n+1) → ℝ) (i : Fin n) : ℝ :=
  ∑ j : Fin (n+1), if j.val ≤ i.val then w j else 0

end SK.Analytic
namespace SK.Analytic

abbrev blockDimension (D N k : ℕ) : ℕ := D+(k+1)*N

def fieldIndex (D N k : ℕ) (b : Fin (k+1)) (i : Fin N) : Fin (blockDimension D N k) :=
  ⟨D+b.val*N+i.val, by
    have hb : (b.val+1)*N ≤ (k+1)*N := Nat.mul_le_mul_right N b.isLt
    dsimp only [blockDimension]
    nlinarith [i.isLt]⟩

def blockLevel (D N k : ℕ) (b : Fin (k+1)) : Fin (blockDimension D N k+1) :=
  ⟨D+(b.val+1)*N, by
    have hb : (b.val+1)*N ≤ (k+1)*N := Nat.mul_le_mul_right N b.isLt
    dsimp only [blockDimension]
    omega⟩

@[simp] theorem fieldIndex_val (D N k : ℕ) (b : Fin (k+1)) (i : Fin N) :
    (fieldIndex D N k b i).val = D+b.val*N+i.val := rfl
@[simp] theorem blockLevel_val (D N k : ℕ) (b : Fin (k+1)) :
    (blockLevel D N k b).val = D+(b.val+1)*N := rfl

def blockAtom (D N k : ℕ) (t : Fin (blockDimension D N k+1)) : ℝ :=
  ∑ b : Fin (k+1), if blockLevel D N k b = t then ((k+1 : ℕ) : ℝ)⁻¹ else 0

def blockMass (D N k : ℕ) := massFromAtoms (blockDimension D N k) (blockAtom D N k)

end SK.Analytic
namespace SK.Analytic

def pairCoefficients (n : ℕ) (p q : Fin n) (a b : ℝ) : Fin n → ℝ :=
  fun t => (if t=p then a else 0)+(if t=q then b else 0)

def sharedFieldCoefficients (D N k : ℕ) (Δ : Fin (k+1) → ℝ) (j : Fin k) (i : Fin N) :=
  pairCoefficients (blockDimension D N k) (fieldIndex D N k j.castSucc i) (fieldIndex D N k j.succ i)
    (Real.sqrt (Δ j.castSucc))⁻¹ (-(Real.sqrt (Δ j.succ))⁻¹)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_GaugeSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK
def logPartitionProxy (β : ℝ) (n : ℕ) : NNReal :=
  ⟨Real.pi ^ 2 * β ^ 2 * n / 8, by positivity⟩

end SK

end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_AverageMeanVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

def blockInteraction {D N k : ℕ} (I : Fin D → Finset (Fin N)) :
    Fin (blockDimension D N k) → Finset (Fin N) :=
  Fin.addCases I (fun t => {(finProdFinEquiv.symm t).2})

def blockCoefficients {D N k : ℕ} (a : Fin D → ℝ) (v : Fin (k+1) → ℝ) :
    Fin (blockDimension D N k) → ℝ := Fin.addCases a (fun t => v (finProdFinEquiv.symm t).1)

end SK.Analytic
namespace SK.Analytic

def sharedBlockWeights (k : ℕ) (Δ : Fin (k+1) → ℝ) (j : Fin k) :=
  pairCoefficients (k+1) j.castSucc j.succ (Real.sqrt (Δ j.castSucc))⁻¹ (-(Real.sqrt (Δ j.succ))⁻¹)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianSpinTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter

noncomputable section
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped MatrixOrder BigOperators
namespace SK.Analytic

section Covariance
variable {Ω I : Type} [MeasurableSpace Ω] [Fintype I]
  {μ : Measure Ω} [IsFiniteMeasure μ]

def covarianceMatrix (X : I → Ω → ℝ) (μ : Measure Ω) : Matrix I I ℝ :=
  fun i j => cov[X i,X j;μ]

def crossCovarianceMatrix (X Y : I → Ω → ℝ) (μ : Measure Ω) : Matrix I I ℝ :=
  fun i j => cov[X i,Y j;μ]

end Covariance
end SK.Analytic
noncomputable section
open scoped BigOperators MatrixOrder
open MeasureTheory ProbabilityTheory Matrix
namespace SK.Analytic
section FiniteCovariance
variable {S I : Type} [Fintype S] [Fintype I]

def finiteMean (p : S → ℝ) (v : S → I → ℝ) : I → ℝ := ∑ s, p s • v s

def finiteCovariance (p : S → ℝ) (v : S → I → ℝ) : Matrix I I ℝ :=
  (∑ s, p s • vecMulVec (v s) (v s)) - vecMulVec (finiteMean p v) (finiteMean p v)

end FiniteCovariance
end SK.Analytic
namespace SK.Analytic
section MixtureCovariance
variable {Ω S : Type} [MeasurableSpace Ω] [Fintype S] {μ : Measure Ω} [IsProbabilityMeasure μ]

def integratedWeights (P : Ω → S → ℝ) (μ : Measure Ω) (s : S) : ℝ := ∫ z, P z s ∂μ

end MixtureCovariance
end SK.Analytic

end
end
end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_ReplicaOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
namespace SK.Analytic
open Matrix
section ReplicaOverlap
variable {S I : Type} [Fintype S] [Fintype I]

def finiteReplicaMoment (p : S → ℝ) (g : S → S → ℝ) : ℝ := ∑ s, ∑ t, p s*p t*g s t

end ReplicaOverlap
end SK.Analytic

end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_SKBlockCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

theorem uniformAtom_sum (k : ℕ) : (∑ _ : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹) = 1 := by
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact mul_inv_cancel₀ (by positivity)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_SpinParameterMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

theorem parameter_contDiff_at_field {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : P × E → ℝ}
    (hf : ContDiff ℝ 2 f) (y : E) : ContDiff ℝ 2 (fun a => f (a,y)) := by
  exact hf.comp (contDiff_id.prodMk contDiff_const)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_AdaptiveODERegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators NNReal
open Set Metric
namespace SK.Analytic

def cumulativeGapMap (k : ℕ) : (Fin (k+1) → ℝ) →L[ℝ] (Fin (k+1) → ℝ) :=
  ContinuousLinearMap.pi (fun j : Fin (k+1) =>
    Fin.cases (motive := fun _ => (Fin (k+1) → ℝ) →L[ℝ] ℝ) (ContinuousLinearMap.proj (0 : Fin (k+1)) : (Fin (k+1) → ℝ) →L[ℝ] ℝ)
      (fun i : Fin k => (ContinuousLinearMap.proj i.succ : (Fin (k+1) → ℝ) →L[ℝ] ℝ)-
        (ContinuousLinearMap.proj i.castSucc : (Fin (k+1) → ℝ) →L[ℝ] ℝ)) j)

@[simp] theorem cumulativeGapMap_zero (k : ℕ) (q : Fin (k+1) → ℝ) :
    cumulativeGapMap k q 0 = q 0 := rfl

@[simp] theorem cumulativeGapMap_succ (k : ℕ) (q : Fin (k+1) → ℝ) (i : Fin k) :
    cumulativeGapMap k q i.succ = q i.succ-q i.castSucc := rfl

def positiveGapScales (k : ℕ) (ε : ℝ) (q : Fin (k+1) → ℝ) : Fin (k+1) → ℝ :=
  fun j => Real.sqrt (max ε (cumulativeGapMap k q j))

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_SpinSiteTensorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def fieldOwner {D N k : ℕ} (i₀ : Fin N) : Fin (blockDimension D N k) → Fin N :=
  Fin.addCases (fun _ => i₀) (fun t => (finProdFinEquiv.symm t).2)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarSpinRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def scalarSpinTerminal (z : ℝ) : ℝ := Real.log (2*Real.cosh z)

def siteScalarCoefficients {D N k : ℕ} (v : Fin (k+1) → ℝ) (i : Fin N)
    (t : Fin (blockDimension D N k)) : ℝ :=
  ∑ b, if fieldIndex D N k b i = t then v b else 0

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def quantileMass (k : ℕ) (j : Fin (k+1)) : ℝ := (j.val:ℝ)/((k+1:ℕ):ℝ)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileClamp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def clampQuantile {k : ℕ} (Q : Fin (k+1) → ℝ) (j : Fin (k+1)) : ℝ := min (Q j) 1

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_ThermodynamicLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

def finiteComparisonError (β : ℝ) (k : ℕ) (η : ℝ) (N : ℕ) : ℝ :=
  (β^2/4)*(20*((k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η))+1/Real.sqrt (k:ℝ))+
    2*(((k+1:ℕ):ℝ)*η)*(1+((k+1:ℕ):ℝ)*η)+4*(((k+1:ℕ):ℝ)*η))

def finiteComparisonErrorLimit (β : ℝ) (k : ℕ) (η : ℝ) : ℝ :=
  (β^2/4)*(20*(1/Real.sqrt (k:ℝ))+
    2*(((k+1:ℕ):ℝ)*η)*(1+((k+1:ℕ):ℝ)*η)+4*(((k+1:ℕ):ℝ)*η))

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_FiniteCoverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def finiteMass {α : Type*} (ν : α → ℝ) (S : Finset α) : ℝ := ∑ x ∈ S, ν x

def conditionalWeights {α : Type*} [DecidableEq α] (ν : α → ℝ)
    (S : Finset α) (x : α) : ℝ := if x ∈ S then ν x/finiteMass ν S else 0

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_UniformCoverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def freshCoverageGain (n : ℕ) (b q : ℝ) : ℝ :=
  b^2*((n:ℝ)-1)/4-Real.log 2-
    Real.sqrt (2*(logPartitionProxy b n:ℝ)*(b^2*(n:ℝ)*q^2/2+Real.log 8))-
    Real.sqrt (2*(logPartitionProxy b n:ℝ)*Real.log 2)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_CoverageGainRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

def coverageGainRate (β e q : ℝ) : ℝ :=
  β^2/4-β*e/2-Real.sqrt (Real.pi^2*(β^2)^2*q^2/8)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_HeatBathChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def siteChoice {n : ℕ} (β : ℝ) (J : Disorder n) (x : Config n) (i : Fin n) (b : Bool) : ℝ :=
  Real.exp (β*spin b*localField J x i)/(2*Real.cosh (β*localField J x i))

theorem siteChoice_pos {n : ℕ} (β : ℝ) (J : Disorder n) (x : Config n) (i : Fin n) (b : Bool) :
    0 < siteChoice β J x i b := by
  apply div_pos (Real.exp_pos _)
  exact mul_pos (by norm_num) (Real.cosh_pos _)

theorem siteChoice_sum {n : ℕ} (β : ℝ) (J : Disorder n) (x : Config n) (i : Fin n) :
    ∑ b : Bool, siteChoice β J x i b = 1 := by
  simp only [siteChoice,Fintype.sum_bool,spin,Bool.false_eq_true,ite_false,ite_true,mul_one,
    mul_neg_one,neg_mul]
  rw [← add_div,Real.cosh_eq]
  have H : Real.exp (β*localField J x i)+Real.exp (-(β*localField J x i)) ≠ 0 := by positivity
  field_simp

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_BankPool
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic

def blockPrior (p B : ℕ) (j : Fin p) : Finset (Fin p) :=
  Finset.univ.filter (fun i => j.val/B*B ≤ i.val ∧ i.val<j.val)

@[simp] theorem mem_blockPrior (p B : ℕ) (i j : Fin p) :
    i∈blockPrior p B j ↔ j.val/B*B ≤ i.val ∧ i.val<j.val := by simp [blockPrior]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_BankCardinality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic

def bankPrefix (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | j+1 => bankPrefix c j+c j+2

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianMassStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem tilted_add_constant {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (c : ℝ) :
    μ.tilted (fun x => f x+c) = μ.tilted f := by
  unfold Measure.tilted
  congr 1
  funext x
  simp_rw [Real.exp_add,integral_mul_const]
  rw [mul_div_mul_right _ _ (Real.exp_ne_zero c)]

def gaussianMassBound (B : ℝ) : ℝ :=
  (∫ y : ℝ, Real.exp ((B+2)* |y|) ∂gaussianReal 0 1) /
    (∫ y : ℝ, Real.exp (-B* |y|) ∂gaussianReal 0 1)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianMassDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem hasDerivAt_dslope_zero_of_analytic {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    HasDerivAt (dslope f 0) (iteratedDeriv 2 f 0/2) 0 := by
  have H := hf.hasFPowerSeriesAt.has_fpower_series_dslope_fslope.hasDerivAt
  change HasDerivAt (dslope f 0)
    ((FormalMultilinearSeries.ofScalars ℝ (fun n => iteratedDeriv n f 0 / n.factorial)).fslope.coeff 1) 0 at H
  norm_num only [FormalMultilinearSeries.coeff_fslope,
    FormalMultilinearSeries.coeff_ofScalars,Nat.reduceAdd,Nat.factorial_two,Nat.cast_ofNat] at H
  exact H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_DslopeLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Topology
open Set
namespace SK.Analytic

theorem dslope_deriv_bound {f : ℝ → ℝ} (hf : ∀ x, AnalyticAt ℝ f x)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ x ∈ Icc (0:ℝ) 1, |iteratedDeriv 2 f x| ≤ K)
    {a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) :
    DifferentiableAt ℝ (dslope f 0) a ∧ |deriv (dslope f 0) a| ≤ K := by
  by_cases ha0 : a = 0
  · subst a
    have H := hasDerivAt_dslope_zero_of_analytic (hf 0)
    refine ⟨H.differentiableAt,?_⟩
    rw [H.deriv,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have H0 := hb 0 (by constructor <;> norm_num)
    linarith
  · have ha' : 0 < a := lt_of_le_of_ne ha.1 (Ne.symm ha0)
    have hfd : Differentiable ℝ f := fun x => (hf x).differentiableAt
    obtain ⟨r,hr,hrf⟩ := exists_deriv_eq_slope f ha' hfd.continuous.continuousOn hfd.differentiableOn
    have hdd : Differentiable ℝ (deriv f) := fun x => (hf x).deriv.differentiableAt
    have hLip := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun x _ => hdd x) (fun x hx => by
        simpa only [iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero,Real.norm_eq_abs] using hb x hx)
      (show r ∈ Icc (0:ℝ) 1 from ⟨hr.1.le,hr.2.le.trans ha.2⟩) ha
    have H := ((hfd a).hasDerivAt.sub_const (f 0)).div (hasDerivAt_id a) ha0
    have he : dslope f 0 =ᶠ[𝓝 a] (fun t => (f t-f 0)/t) := by
      filter_upwards [eventually_ne_nhds ha0] with t ht
      simp only [dslope_of_ne _ ht,slope_def_field,sub_zero]
    have H' := H.congr_of_eventuallyEq he
    refine ⟨H'.differentiableAt,?_⟩
    rw [H'.deriv]
    simp only [id_eq]
    have heq : (deriv f a*a-(f a-f 0)*1)/a^2 = (deriv f a-deriv f r)/a := by
      rw [hrf,sub_zero]
      field_simp
    rw [heq,abs_div,abs_of_pos ha']
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hr.2)] at hLip
    apply (div_le_iff₀ ha').mpr
    exact hLip.trans (mul_le_mul_of_nonneg_left (by linarith [hr.1]) hK)

theorem dslope_mass_lipschitz {f : ℝ → ℝ} (hf : ∀ x, AnalyticAt ℝ f x)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ x ∈ Icc (0:ℝ) 1, |iteratedDeriv 2 f x| ≤ K)
    {a b : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (hb' : b ∈ Icc (0:ℝ) 1) :
    |dslope f 0 b-dslope f 0 a| ≤ K*|b-a| := by
  have H := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun x hx => (dslope_deriv_bound hf hK hb hx).1)
    (fun x hx => by simpa only [Real.norm_eq_abs] using (dslope_deriv_bound hf hK hb hx).2) ha hb'
  simpa only [Real.norm_eq_abs] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarSemigroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal
open MeasureTheory ProbabilityTheory
namespace SK.Analytic

theorem integral_gaussian_mul (v : ℝ) {g : ℝ → ℝ} (hg : StronglyMeasurable g) :
    (∫ y, g (v*y) ∂gaussianReal 0 1) =
      ∫ y, g y ∂gaussianReal 0 (NNReal.mk (v^2) (sq_nonneg v)) := by
  have hμ := gaussianReal_map_const_mul (μ := 0) (v := 1) v
  simp only [mul_zero,mul_one] at hμ
  rw [← hμ,integral_map (by fun_prop) hg.aestronglyMeasurable]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_DyadicScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def dyadicIntervals (α : ℝ → ℝ) : ℕ → ℝ → ℝ≥0 → List (ℝ × ℝ≥0)
  | 0,s,t => [(α s,t)]
  | n+1,s,t => dyadicIntervals α n s (t/2) ++
      dyadicIntervals α n (s+(t:ℝ)/2) (t/2)

theorem dyadicIntervals_mem_bounds {α : ℝ → ℝ} (hα : Monotone α)
    (n : ℕ) (s : ℝ) (t : ℝ≥0) {p : ℝ × ℝ≥0} (hp : p ∈ dyadicIntervals α n s t) :
    α s ≤ p.1 ∧ p.1 ≤ α (s+t) ∧ p.2 ≤ t := by
  induction n generalizing s t with
  | zero =>
    simp only [dyadicIntervals,List.mem_singleton] at hp
    subst p
    exact ⟨le_rfl,hα (by linarith [t.coe_nonneg]),le_rfl⟩
  | succ n ih =>
    simp only [dyadicIntervals,List.mem_append] at hp
    have ht : t/2 ≤ t := by exact div_le_self (show (0:ℝ≥0) ≤ t from bot_le) (by norm_num)
    have htc : ((t/2:ℝ≥0):ℝ)=(t:ℝ)/2 := by norm_num
    rcases hp with hp|hp
    · obtain ⟨h₁,h₂,h₃⟩ := ih s (t/2) hp
      exact ⟨h₁,h₂.trans (hα (by rw [htc]; linarith [t.coe_nonneg])),h₃.trans ht⟩
    · obtain ⟨h₁,h₂,h₃⟩ := ih (s+(t:ℝ)/2) (t/2) hp
      refine ⟨(hα (by linarith [t.coe_nonneg])).trans h₁,?_,h₃.trans ht⟩
      simpa only [htc,show s+(t:ℝ)/2+(t:ℝ)/2=s+t by ring] using h₂

theorem dyadicIntervals_mass_bounds {α : ℝ → ℝ} (hα : ∀ s, α s ∈ Icc (0:ℝ) 1)
    (n : ℕ) (s : ℝ) (t : ℝ≥0) {p : ℝ × ℝ≥0} (hp : p ∈ dyadicIntervals α n s t) :
    p.1 ∈ Icc (0:ℝ) 1 := by
  induction n generalizing s t with
  | zero =>
    simp only [dyadicIntervals,List.mem_singleton] at hp
    subst p
    exact hα s
  | succ n ih =>
    simp only [dyadicIntervals,List.mem_append] at hp
    exact hp.elim (ih s (t/2)) (ih (s+(t:ℝ)/2) (t/2))

def scalarTimeMassConstant (β : ℝ) : ℝ := gaussianMassBound |β| * β^2

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_TerminalPathStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem hierarchyAtom_nonneg (n : ℕ) (m : Fin n → ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ u) (hmono : Monotone m) (j : Fin (n+1)) :
    0 ≤ hierarchyAtom n m u j := by
  induction n generalizing u with
  | zero => exact hu
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [hierarchyAtom, Fin.lastCases_last]
      exact sub_nonneg.mpr (hmu (Fin.last n))
    · simp only [hierarchyAtom, Fin.lastCases_castSucc]
      exact ih (fun i => m i.castSucc) (hm (Fin.last n)) (fun i => hm i.castSucc)
        (fun i => hmono (Fin.le_last _))
        (fun _ _ h => hmono (Fin.castSucc_le_castSucc_iff.mpr h)) i

theorem hierarchyAtom_sum (n : ℕ) (m : Fin n → ℝ) (u : ℝ) :
    ∑ j, hierarchyAtom n m u j = u := by
  induction n generalizing u with
  | zero => simp [hierarchyAtom]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [hierarchyAtom, Fin.lastCases_castSucc, Fin.lastCases_last, ih]
    ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_RootSusceptibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem exp_two_mul_sub_one_bound {a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) :
    Real.exp (2*a)-1≤2*Real.exp 2*a := by
  have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (Real.hasDerivAt_exp z).hasDerivWithinAt)
    (fun z (hz : z ∈ Icc (0:ℝ) 2) => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos z)]
      exact Real.exp_le_exp.mpr hz.2)
    (convex_Icc (0:ℝ) 2)
    (show (0:ℝ) ∈ Icc (0:ℝ) 2 by constructor <;> norm_num)
    (show 2*a ∈ Icc (0:ℝ) 2 by constructor <;> linarith [ha.1,ha.2])
  simp only [Real.norm_eq_abs,Real.exp_zero,sub_zero,abs_of_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) ha.1)] at H
  have hi := (le_abs_self (Real.exp (2*a)-1)).trans H
  nlinarith

def susceptibilityLipschitzConstant : ℝ≥0 := ⟨2+4*Real.exp 2,by positivity⟩

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_DerivativeStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped Topology NNReal
namespace SK.Analytic

theorem derivative_bound_of_uniform_value_and_lipschitz
    (f f' : ℝ → ℝ) (K : ℝ≥0) (ε : ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hK : LipschitzWith K f')
    (hε : ∀ x, |f x| ≤ ε) (x h : ℝ) (hh : 0 < h) :
    |f' x| ≤ 2*ε/h+(K:ℝ)*h := by
  let F := fun t : ℝ => f t-f' x*t
  have hF (t : ℝ) : HasDerivAt F (f' t-f' x) t := by
    convert (hf t).sub ((hasDerivAt_id t).const_mul (f' x)) using 1 <;>
      first | rfl | simp only [mul_one]
  have hb (t : ℝ) (ht : t ∈ Set.Icc x (x+h)) : ‖f' t-f' x‖ ≤ (K:ℝ)*h := by
    have H := hK.norm_sub_le t x
    apply H.trans
    apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2]
  have H := (convex_Icc x (x+h)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hF t).hasDerivWithinAt) hb
    (show x ∈ Set.Icc x (x+h) from ⟨le_rfl,by linarith⟩)
    (show x+h ∈ Set.Icc x (x+h) from ⟨by linarith,le_rfl⟩)
  have he : F (x+h)-F x = f (x+h)-f x-f' x*h := by dsimp [F]; ring
  rw [he,Real.norm_eq_abs,Real.norm_eq_abs,add_sub_cancel_left,abs_of_pos hh] at H
  have hy := abs_le.mp (hε (x+h))
  have hx := abs_le.mp (hε x)
  have hE := abs_le.mp H
  have H' : |f' x*h| ≤ 2*ε+(K:ℝ)*h*h := by
    rw [abs_le]
    constructor <;> linarith
  rw [abs_mul,abs_of_pos hh] at H'
  have HD := (le_div_iff₀ hh).mpr H'
  apply HD.trans_eq
  rw [add_div,mul_div_cancel_right₀ _ hh.ne']

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_DyadicSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem dyadicIntervals_pairwise {α : ℝ → ℝ} (hα : Monotone α)
    (n : ℕ) (s : ℝ) (t : ℝ≥0) :
    (dyadicIntervals α n s t).Pairwise (fun p q => p.1 ≤ q.1) := by
  induction n generalizing s t with
  | zero => exact List.pairwise_singleton _ _
  | succ n ih =>
    apply List.pairwise_append.mpr
    refine ⟨ih s (t/2),ih (s+(t:ℝ)/2) (t/2),?_⟩
    intro p hp q hq
    have H := (dyadicIntervals_mem_bounds hα n s (t/2) hp).2.1
    have H' := (dyadicIntervals_mem_bounds hα n (s+(t:ℝ)/2) (t/2) hq).1
    norm_num only [NNReal.coe_div,NNReal.coe_ofNat] at H
    exact H.trans H'

theorem scalarTimeChain_mass_monotone (l : List (ℝ × ℝ≥0))
    (h : l.Pairwise (fun p q => p.1 ≤ q.1)) : Monotone (fun i => (l.get i).1) := by
  intro i j hij
  rcases hij.eq_or_lt with he|he
  · exact he ▸ le_rfl
  · exact List.pairwise_iff_get.mp h i j he

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_UniformDerivativeLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Topology NNReal
open Filter Set
namespace SK.Analytic

theorem geometric_uniform_limit {X : Type*} (F : ℕ → X → ℝ) {C r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1)
    (hF : ∀ n x, |F (n+1) x-F n x| ≤ C*r^n) :
    TendstoUniformly F (fun x => limUnder atTop (fun n => F n x)) atTop ∧
      ∀ n x, |F n x-limUnder atTop (fun k => F k x)| ≤ C*r^n/(1-r) := by
  have hs : Summable (fun n : ℕ => C*r^n) := (summable_geometric_of_lt_one hr hr1).mul_left C
  have hd (n : ℕ) (x : X) : dist (F n x) (F (n+1) x) ≤ C*r^n := by
    simpa only [Real.dist_eq,abs_sub_comm] using hF n x
  have ht (x : X) : Tendsto (fun n => F n x) atTop (𝓝 (limUnder atTop (fun n => F n x))) :=
    tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete
      (cauchySeq_of_dist_le_of_summable _ (fun n => hd n x) hs))
  have hb (n : ℕ) (x : X) : |F n x-limUnder atTop (fun k => F k x)| ≤ C*r^n/(1-r) := by
    have H := dist_le_tsum_of_dist_le_of_tendsto _ (fun k => hd k x) hs (ht x) n
    have he : (∑' k : ℕ, C*r^(n+k))=C*r^n/(1-r) := by
      simp only [pow_add,← mul_assoc,tsum_mul_left,tsum_geometric_of_lt_one hr hr1,div_eq_mul_inv]
    simpa only [Real.dist_eq,he] using H
  refine ⟨?_,hb⟩
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hlim : Tendsto (fun n : ℕ => C*r^n/(1-r)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).const_mul C).div_const (1-r)
  filter_upwards [(tendsto_order.mp hlim).2 ε hε] with n hn x
  rw [Real.dist_eq,abs_sub_comm]
  exact (hb n x).trans_lt hn

theorem uniformCauchySeq_derivative {F D : ℕ → ℝ → ℝ} (K : ℝ≥0)
    (hD : ∀ n x, HasDerivAt (F n) (D n x) x)
    (hLip : ∀ n, LipschitzWith K (D n))
    (hF : UniformCauchySeqOn F atTop univ) : UniformCauchySeqOn D atTop univ := by
  rw [Metric.uniformCauchySeqOn_iff] at hF ⊢
  intro ε hε
  let h : ℝ := ε/(8*((K:ℝ)+1))
  have hh : 0<h := div_pos hε (by positivity)
  have hke : 8*((K:ℝ)+1)*h=ε := by dsimp [h]; field_simp
  let δ : ℝ := ε*h/8
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨N,hN⟩ := hF δ hδ
  refine ⟨N,?_⟩
  intro m hm n hn x _
  have hb (z : ℝ) : |F m z-F n z| ≤ δ := by
    exact (hN m hm n hn z (mem_univ _)).le
  have H := derivative_bound_of_uniform_value_and_lipschitz _ _ (K+K) δ
    (fun z => (hD m z).sub (hD n z)) ((hLip m).sub (hLip n)) hb x h hh
  have he : 2*δ/h=ε/4 := by dsimp [δ]; field_simp; ring
  rw [he,NNReal.coe_add] at H
  rw [Real.dist_eq]
  have hk := K.coe_nonneg
  nlinarith

theorem uniformCauchySeq_limUnder {X : Type*} {F : ℕ → X → ℝ}
    (hF : UniformCauchySeqOn F atTop univ) :
    TendstoUniformly F (fun x => limUnder atTop (fun n => F n x)) atTop := by
  apply tendstoUniformlyOn_univ.mp
  apply hF.tendstoUniformlyOn_of_tendsto
  intro x _
  exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hF.cauchySeq (mem_univ x)))

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarGeneralTerminal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def scalarTimeMassConstantK (β : ℝ) (K : ℝ≥0) : ℝ :=
  gaussianMassBound ((K:ℝ)*|β|)*(K:ℝ)^2*β^2

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_TerminalPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def primitivePerturbation (f G : ℝ → ℝ) (a y : ℝ) : ℝ :=
  f y+G (y+a)-G y

theorem primitivePerturbation_lipschitz {f G : ℝ → ℝ} {K B : ℝ≥0}
    (hf : LipschitzWith K f) (hG : LipschitzWith B G) (a : ℝ) :
    LipschitzWith (K+B+B) (primitivePerturbation f G a) := by
  have ht : LipschitzWith B (fun y => G (y+a)) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [Real.dist_eq,add_sub_add_right_eq_sub] using hG.dist_le_mul (y+a) (z+a)
  exact (hf.add ht).sub hG

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarTiltedExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

@[simp] theorem primitivePerturbation_zero (f G : ℝ → ℝ) : primitivePerturbation f G 0=f := by
  funext y
  simp only [primitivePerturbation,add_zero,add_sub_cancel_right]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_CommonBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def commonBranchEmbedding : ℝ →L[ℝ] (ℝ × ℝ) × ℝ :=
  ((ContinuousLinearMap.id ℝ ℝ).prod 0).prod (ContinuousLinearMap.id ℝ ℝ)

@[simp] theorem commonBranchEmbedding_apply (x : ℝ) : commonBranchEmbedding x=((x,0),x) := rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_VectorBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def vectorTranslation (v : E) : (E × ℝ) →L[ℝ] E :=
  ContinuousLinearMap.fst ℝ E ℝ + (ContinuousLinearMap.snd ℝ E ℝ).smulRight v

end Vector

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_FiniteCovarianceInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

section
variable {S : Type} [Fintype S] [Nonempty S]

def partialObservableCovariance (n : ℕ) (O : Fin n → S → ℝ) (b : Fin n → ℝ)
    (j : Fin (n+1)) (s t : S) : ℝ :=
  ∑ i : Fin n, if i.val < j.val then b i*(O i s*O i t) else 0

end
end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_FiniteCovarianceComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

section
variable {S : Type} [Fintype S] [Nonempty S]

def interpolationCoefficient (n : ℕ) (I : Fin n → Bool) (t : ℝ) (i : Fin n) : ℝ :=
  if I i then Real.sqrt t else Real.sqrt (1-t)

def interpolationRate (n : ℕ) (I : Fin n → Bool) (i : Fin n) : ℝ :=
  if I i then 1/2 else -(1/2)

end
end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_BlockObservable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

variable {S : Type}

def blockObservable {D N k : ℕ} (H : Fin D → S → ℝ)
    (F : Fin (k+1) → Fin N → S → ℝ) : Fin (blockDimension D N k) → S → ℝ :=
  Fin.addCases H (fun t => F (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2)

def blockInterpolationChoice (D N k : ℕ) : Fin (blockDimension D N k) → Bool :=
  Fin.addCases (fun _ => true) (fun _ => false)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedBlockMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def weightedBlockAtom (D N k : ℕ) (w : Fin (k+1) → ℝ)
    (t : Fin (blockDimension D N k+1)) : ℝ :=
  ∑ b : Fin (k+1), if blockLevel D N k b=t then w b else 0

def weightedBlockMass (D N k : ℕ) (w : Fin (k+1) → ℝ) :
    Fin (blockDimension D N k) → ℝ :=
  massFromAtoms (blockDimension D N k) (weightedBlockAtom D N k w)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_BlockSiteEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def blockSiteEmbedding (D N r k : ℕ) (i : Fin N) (j : Fin ((k+1)*r)) :
    Fin (blockDimension D (N*r) k) :=
  fieldIndex D (N*r) k (finProdFinEquiv.symm j).1
    (finProdFinEquiv (i,(finProdFinEquiv.symm j).2))

def blockSiteOwner {D N r k : ℕ} (i₀ : Fin N) : Fin (blockDimension D (N*r) k) → Fin N :=
  Fin.addCases (fun _ => i₀) (fun t => (finProdFinEquiv.symm (finProdFinEquiv.symm t).2).1)

def siteBlockMass (r k : ℕ) (w : Fin (k+1) → ℝ) (j : Fin ((k+1)*r)) : ℝ :=
  ∑ l, if l<(finProdFinEquiv.symm j).1 then w l else 0

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_EmbeddedSites
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
section
variable {A : Type} [Fintype A] [Nonempty A]

def siteValueTerminal (c : A → ℝ) : (A → ℝ) → ℝ :=
  affineLogPartition c (fun a => ContinuousLinearMap.proj a)

def embeddedVector {n r : ℕ} (e : Fin r → Fin n) (V : Fin r → A → ℝ)
    (t : Fin n) : A → ℝ := ∑ j, if e j=t then V j else 0

end

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_BlockSiteFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
section
variable {A S : Type} [Fintype A] [Nonempty A] [Fintype S] [Nonempty S]

def siteBlockObservables {N r k : ℕ} (V : Fin ((k+1)*r) → A → ℝ) :
    Fin (k+1) → Fin (N*r) → (Fin N → A) → ℝ :=
  fun b p s => V (finProdFinEquiv (b,(finProdFinEquiv.symm p).2)) (s (finProdFinEquiv.symm p).1)

end

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_MatrixCovarianceAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def matrixFieldFeature (N d r : ℕ) (β : ℝ) (B : Fin r → Fin d → ℝ)
    (X : Fin N → Fin d → ℝ) (p : Fin N × Fin r) : ℝ :=
  β*∑ a, B p.2 a*X p.1 a

def factorCovariance (d r : ℕ) (B : Fin r → Fin d → ℝ) (a b : Fin d) : ℝ :=
  ∑ u, B u a*B u b

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_MatrixGuerraKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def matrixInner (d : ℕ) (Q R : Fin d → Fin d → ℝ) : ℝ := ∑ a, ∑ b, Q a b*R a b

def matrixSquare (d : ℕ) (Q : Fin d → Fin d → ℝ) : ℝ := ∑ a, ∑ b, (Q a b)^2

def factorPath (d r k : ℕ) (B : Fin (k+1) → Fin r → Fin d → ℝ)
    (j : Fin (k+1)) (a b : Fin d) : ℝ :=
  ∑ l, if l ≤ j then factorCovariance d r (B l) a b else 0

section
variable {S : Type} [Fintype S] [Nonempty S]

def matrixFieldObservables (N d r k : ℕ) (β : ℝ) (B : Fin (k+1) → Fin r → Fin d → ℝ)
    (X : S → Fin N → Fin d → ℝ) : Fin (k+1) → Fin (N*r) → S → ℝ :=
  fun l u s => matrixFieldFeature N d r β (B l) (X s) (finProdFinEquiv.symm u)

end
end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_MatrixGuerraEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

variable {A S : Type} [Fintype A] [Nonempty A] [Fintype S] [Nonempty S]

def matrixSiteWeight {d : ℕ} (Λ : Fin d → Fin d → ℝ) (v : A → Fin d → ℝ) (a : A) : ℝ :=
  ∑ u, ∑ t, Λ u t*v a u*v a t

def matrixSiteVector {d r k : ℕ} (β : ℝ) (B : Fin (k+1) → Fin r → Fin d → ℝ)
    (v : A → Fin d → ℝ) (j : Fin ((k+1)*r)) (a : A) : ℝ :=
  β*∑ u, B (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2 u*v a u

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyMassPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def zeroInitialAtoms (k : ℕ) (m : Fin (k+1) → ℝ) : Fin (k+1) → ℝ :=
  hierarchyAtom k (fun i => m i.succ) 1

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_FinitePrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def finitePrefix {n : ℕ} (v : Fin n → ℝ) (j : Fin n) : ℝ := ∑ l, if l ≤ j then v l else 0

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_RankOneMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def rankOnePath {n : ℕ} (d : ℕ) (b : Fin n → Fin d → ℝ) (j : Fin n) : Fin d → Fin d → ℝ :=
  fun u v => ∑ i, if i ≤ j then b i u*b i v else 0

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_MatrixChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

section Penalty
variable {E : Type} [AddCommMonoid E]

def chainSum (l : List (ℝ × E)) : E := (l.map Prod.snd).sum

@[simp] theorem chainSum_nil : chainSum ([] : List (ℝ × E))=0 := rfl
@[simp] theorem chainSum_cons (p : ℝ × E) (l : List (ℝ × E)) :
    chainSum (p::l)=p.2+chainSum l := rfl

def strictPrefix {n : ℕ} (v : Fin n → E) (i : Fin n) : E := ∑ j,if j < i then v j else 0

end Penalty

def rankOneMatrix {d : ℕ} (b : Fin d → ℝ) : Fin d → Fin d → ℝ := fun i j => b i*b j

def matrixChainCovariance {d : ℕ} (l : List (ℝ × (Fin d → ℝ))) : Fin d → Fin d → ℝ :=
  chainSum (l.map (fun p => (p.1,rankOneMatrix p.2)))

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TriplePerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def tripleSymmetricMatrix (a b r q : ℝ) : Fin 3 → Fin 3 → ℝ :=
  !![a,r,r; r,b,q; r,q,b]

def tripleImbalance : Fin 3 → Fin 3 → ℝ := !![0,1,-1; 1,0,0; -1,0,0]
def tripleQuadraticCorrection : Fin 3 → Fin 3 → ℝ := !![0,0,0; 0,1,-1; 0,-1,1]

def triplePerturbedMatrix (a b r q δ g G : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j => tripleSymmetricMatrix a b r q i j+δ*g*tripleImbalance i j+
    δ^2*G*tripleQuadraticCorrection i j

def tripleGram (r δ q : ℝ) : Fin 3 → Fin 3 → ℝ :=
  !![1,r+δ,r-δ; r+δ,1,q; r-δ,q,1]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleClockAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def tripleClockMatrix (a b c r q : ℝ) : Fin 3 → Fin 3 → ℝ :=
  !![a,r,r; r,b,q; r,q,c]

def tripleClockPerturbed (a b c r q δ g G : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j => tripleClockMatrix a b c r q i j+δ*g*tripleImbalance i j+
    δ^2*G*tripleQuadraticCorrection i j

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def tripleCommonSchedule (l : List (ℝ × ℝ)) : List (ℝ × (Fin 3 → ℝ)) :=
  l.map (fun p => (p.1/3,![p.2,p.2,p.2]))

def tripleTailBlock (p : ℝ × ℝ) : List (ℝ × (Fin 3 → ℝ)) :=
  [(p.1,![p.2,0,0]),(p.1,![0,p.2,0]),(p.1,![0,0,p.2])]

def tripleTailSchedule (l : List (ℝ × ℝ)) : List (ℝ × (Fin 3 → ℝ)) := l.flatMap tripleTailBlock

@[simp] theorem matrixChainCovariance_nil {d : ℕ} : matrixChainCovariance ([] : List (ℝ × (Fin d → ℝ)))=0 := rfl
@[simp] theorem matrixChainCovariance_cons {d : ℕ} (p : ℝ × (Fin d → ℝ)) (l : List (ℝ × (Fin d → ℝ))) :
    matrixChainCovariance (p::l)=rankOneMatrix p.2+matrixChainCovariance l := rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleTailValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def tripleCoordinate (i : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i

@[simp] theorem tripleCoordinate_apply (i : Fin 3) (x : Fin 3 → ℝ) : tripleCoordinate i x=x i := rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarOneAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

def scalarMagnetization (z : ℝ) : ℝ := Real.sinh z/Real.cosh z

theorem scalarMagnetization_derivative_identity (z : ℝ) :
    1/(Real.cosh z)^2 = 1-(scalarMagnetization z)^2 := by
  have H := Real.cosh_sq_sub_sinh_sq z
  unfold scalarMagnetization
  field_simp
  nlinarith

theorem scalarMagnetization_sq_le_one (z : ℝ) : (scalarMagnetization z)^2 ≤ 1 := by
  have H := scalarMagnetization_derivative_identity z
  have := div_nonneg (by norm_num : (0:ℝ) ≤ 1) (sq_nonneg (Real.cosh z))
  linarith

theorem scalarMagnetization_abs_le_one (z : ℝ) : |scalarMagnetization z| ≤ 1 :=
  (sq_le_one_iff_abs_le_one _).mp (scalarMagnetization_sq_le_one z)

theorem scalarSpinTerminal_hasDerivAt (z : ℝ) :
    HasDerivAt scalarSpinTerminal (scalarMagnetization z) z := by
  have H := ((Real.hasDerivAt_cosh z).const_mul 2).log
    (mul_pos (by norm_num : (0:ℝ)<2) (Real.cosh_pos z)).ne'
  apply H.congr_deriv
  dsimp [scalarMagnetization]
  field_simp

theorem scalarSpinTerminal_lipschitz : LipschitzWith 1 scalarSpinTerminal := by
  rw [← lipschitzOnWith_univ]
  apply (convex_univ : Convex ℝ (Set.univ : Set ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun z _ => (scalarSpinTerminal_hasDerivAt z).hasDerivWithinAt)
  intro z _
  change ‖scalarMagnetization z‖ ≤ (1:ℝ)
  simpa only [Real.norm_eq_abs] using scalarMagnetization_abs_le_one z

def scalarGaussianValue (v : ℝ) : ℝ := ∫ y, scalarSpinTerminal (v*y) ∂gaussianReal 0 1

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarSymmetricTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def symmetricIncrement (f : ℝ → ℝ) (z h : ℝ) : ℝ := f (z+h)+f (z-h)-2*f z

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleRetained
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

abbrev TripleRetainedState := (ℝ × ℝ) × ℝ

def retainedSingleton : TripleRetainedState →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)
def retainedNoise : TripleRetainedState →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)
def retainedPair : TripleRetainedState →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ

def tripleRetainedEmbedding (δ : ℝ) : TripleRetainedState →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi ![retainedSingleton,retainedPair+δ • retainedNoise,retainedPair-δ • retainedNoise]

@[simp] theorem tripleRetainedEmbedding_apply (δ : ℝ) (x : TripleRetainedState) :
    tripleRetainedEmbedding δ x=![x.1.1,x.2+δ*x.1.2,x.2-δ*x.1.2] := by
  funext i; fin_cases i <;> rfl

def tripleRetainedCommon (c : List (ℝ × ℝ)) : List (ℝ × TripleRetainedState) :=
  c.map (fun p => (p.1/3,((p.2,0),p.2)))

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedListBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def zeroNoiseEmbedding : ℝ →L[ℝ] (ℝ × ℝ) := (ContinuousLinearMap.id ℝ ℝ).prod 0

@[simp] theorem zeroNoiseEmbedding_apply (x : ℝ) : zeroNoiseEmbedding x=(x,0) := rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarEarlyMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def scalarPrefixVector (n : ℕ) (v : Fin n → ℝ) (j : Fin (n+1)) (i : Fin n) : ℝ :=
  if i.val < j.val then v i else 0

def scalarPrefixVariance (n : ℕ) (v : Fin n → ℝ) (j : Fin (n+1)) : ℝ :=
  ∑ i, (scalarPrefixVector n v j i)^2

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowClockAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def narrowClockPerturbed (a b c r q δ g y K : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j => tripleClockMatrix a b c r q i j+
    δ*(!![0,g,-g;g,2*y,0;-g,0,-2*y] : Fin 3 → Fin 3 → ℝ) i j+
    δ^2*K*tripleQuadraticCorrection i j

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def narrowCommonSchedule (δ : ℝ) (l : List (ℝ × (ℝ × ℝ))) : List (ℝ × (Fin 3 → ℝ)) :=
  l.map (fun p => (p.1/3,![p.2.1,p.2.1+δ*p.2.2,p.2.1-δ*p.2.2]))

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleFiniteExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def tripleExpansionConstant (a : ℝ) : ℝ :=
  ((2*(susceptibilityLipschitzConstant:ℝ)*(1+2/a^2)+32/a^2)*2)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleScheduleEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

@[simp] theorem tripleClockMatrix_zero : tripleClockMatrix 0 0 0 0 0=0 := by
  funext i j; fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem tripleClockPerturbed_zero (a b c r q δ : ℝ) :
    tripleClockPerturbed a b c r q δ 0 0=tripleClockMatrix a b c r q := by
  ext i j; simp [tripleClockPerturbed]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_BoundedPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Topology NNReal ContDiff
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def boundedPrimitive (g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in 0..x, g y

theorem boundedPrimitive_hasDerivAt {g : ℝ → ℝ} (hg : Continuous g) (x : ℝ) :
    HasDerivAt (boundedPrimitive g) (g x) x :=
  intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 x)
    hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt

theorem boundedPrimitive_lipschitz {g : ℝ → ℝ} (hg : Continuous g) {B : ℝ≥0}
    (hB : ∀ x, |g x| ≤ B) : LipschitzWith B (boundedPrimitive g) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (boundedPrimitive_hasDerivAt hg x).differentiableAt)
  intro x
  rw [(boundedPrimitive_hasDerivAt hg x).deriv]
  exact_mod_cast hB x

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_PartitionChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def partitionTimeChain (n : ℕ) (q : Fin (n+1) → ℝ) (hq : Monotone q)
    (m : Fin n → ℝ) : List (ℝ × ℝ≥0) :=
  List.ofFn (fun i : Fin n => (m i,NNReal.mk (q i.succ-q i.castSucc) (sub_nonneg.mpr (hq (Fin.castSucc_le_succ i)))))

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarAtomic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def quantileAtomLaw (k : ℕ) (Q : Fin (k+1) → ℝ) : Measure ℝ :=
  ∑ j : Fin (k+1), ENNReal.ofReal (((k+1:ℕ):ℝ)⁻¹) • Measure.dirac (Q j)

theorem quantileAtomLaw_apply (k : ℕ) (Q : Fin (k+1) → ℝ) (s : Set ℝ) [DecidablePred (· ∈ s)] :
    quantileAtomLaw k Q s = ENNReal.ofReal (∑ j : Fin (k+1), if Q j ∈ s then ((k+1:ℕ):ℝ)⁻¹ else 0) := by
  classical
  rw [quantileAtomLaw,Measure.finsetSum_apply,ENNReal.ofReal_sum_of_nonneg (fun j _ => by split_ifs <;> positivity)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Measure.smul_apply,smul_eq_mul,Measure.dirac_apply,Set.indicator_apply,Pi.one_apply]
  split_ifs <;> simp

instance quantileAtomLaw_probability (k : ℕ) (Q : Fin (k+1) → ℝ) : IsProbabilityMeasure (quantileAtomLaw k Q) := by
  constructor
  rw [quantileAtomLaw_apply]
  simp only [Set.mem_univ,ite_true,uniformAtom_sum,ENNReal.ofReal_one]

def quantileCDF (k : ℕ) (Q : Fin (k+1) → ℝ) (s : ℝ) : ℝ := (quantileAtomLaw k Q).real (Set.Iic s)

theorem quantileCDF_formula (k : ℕ) (Q : Fin (k+1) → ℝ) (s : ℝ) :
    quantileCDF k Q s = ∑ j : Fin (k+1), if Q j ≤ s then ((k+1:ℕ):ℝ)⁻¹ else 0 := by
  rw [quantileCDF,Measure.real,quantileAtomLaw_apply,ENNReal.toReal_ofReal]
  · rfl
  · exact Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem quantileCDF_bounds (k : ℕ) (Q : Fin (k+1) → ℝ) (s : ℝ) :
    quantileCDF k Q s ∈ Icc (0:ℝ) 1 := by
  rw [quantileCDF_formula]
  constructor
  · exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)
  · rw [← uniformAtom_sum k]
    exact Finset.sum_le_sum (fun _ _ => by split_ifs <;> first | exact le_rfl | positivity)

theorem monotone_cons_zero_quantiles {k : ℕ} (Q : Fin (k+1) → ℝ)
    (hQ : Monotone Q) (h0 : 0 ≤ Q 0) : Monotone (Fin.cons (α := fun _ => ℝ) 0 Q) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact h0
  · exact hQ (Fin.castSucc_le_succ j)

theorem quantileCDF_on_interval {k : ℕ} (Q : Fin (k+1) → ℝ) (hQ : Monotone Q)
    (i : Fin (k+1)) (z : ℝ) (hz : z ∈ Ico (Fin.cons (α := fun _ => ℝ) 0 Q i.castSucc) (Q i)) :
    quantileCDF k Q z=quantileMass k i := by
  have he (j : Fin (k+1)) : Q j ≤ z ↔ j < i := by
    constructor
    · intro hj
      by_contra hji
      have H := hQ (le_of_not_gt hji)
      linarith [hz.2]
    · intro hji
      cases i using Fin.cases with
      | zero => simp at hji
      | succ l =>
        have hj : j ≤ l.castSucc := by simpa only [Fin.le_def,Fin.lt_def,Fin.val_castSucc] using (Nat.le_of_lt_succ hji)
        exact (hQ hj).trans hz.1
  rw [quantileCDF_formula]
  simp_rw [he]
  rw [← Finset.sum_filter]
  have hs : (Finset.univ.filter (fun j : Fin (k+1) => j < i))=Finset.Iio i := by ext j; simp
  rw [hs,Finset.sum_const,Fin.card_Iio]
  simp only [nsmul_eq_mul,quantileMass,div_eq_mul_inv]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileMinimizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def admissibleQuantiles (k : ℕ) : Set (Fin (k+1) → ℝ) :=
  {Q | Monotone Q ∧ ∀ j, Q j ∈ Set.Icc 0 1}

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_DyadicCDFStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def dyadicCDFDistance (α γ : ℝ → ℝ) : ℕ → ℝ → ℝ≥0 → ℝ
  | 0,s,t => (t:ℝ)*|α s-γ s|
  | n+1,s,t => dyadicCDFDistance α γ n s (t/2) +
      dyadicCDFDistance α γ n (s+(t:ℝ)/2) (t/2)

theorem dyadicCDFDistance_integral_bound {α γ : ℝ → ℝ}
    (hα : Monotone α) (hγ : Monotone γ) (n : ℕ) (s : ℝ) (t : ℝ≥0) :
    dyadicCDFDistance α γ n s t ≤ (∫ z in s..s+t, |α z-γ z|) +
      (t:ℝ)/(2:ℝ)^n*((α (s+t)-α s)+(γ (s+t)-γ s)) := by
  have hi (a b : ℝ) : IntervalIntegrable (fun z => |α z-γ z|) volume a b :=
    (hα.intervalIntegrable.sub hγ.intervalIntegrable).abs
  induction n generalizing s t with
  | zero =>
    have hb (z : ℝ) (hz : z ∈ Icc s (s+t)) :
        |α s-γ s| ≤ |α z-γ z|+((α (s+t)-α s)+(γ (s+t)-γ s)) := by
      have H := abs_sub_le (α s) (α z) (γ s)
      have H' := abs_sub_le (α z) (γ z) (γ s)
      rw [abs_of_nonpos (sub_nonpos.mpr (hα hz.1))] at H
      rw [abs_of_nonneg (sub_nonneg.mpr (hγ hz.1))] at H'
      linarith [hα hz.2,hγ hz.2]
    have H := intervalIntegral.integral_mono_on (show s ≤ s+(t:ℝ) by linarith [t.coe_nonneg])
      (intervalIntegrable_const) ((hi s (s+t)).add intervalIntegrable_const) hb
    rw [intervalIntegral.integral_add (hi s (s+t)) intervalIntegrable_const,
      intervalIntegral.integral_const,intervalIntegral.integral_const] at H
    simpa only [dyadicCDFDistance,pow_zero,div_one,add_sub_cancel_left,smul_eq_mul] using H
  | succ n ih =>
    have hc : ((t/2:ℝ≥0):ℝ)=(t:ℝ)/2 := by norm_num
    have he : s+(t:ℝ)/2+(t:ℝ)/2=s+t := by ring
    have H := add_le_add (ih s (t/2)) (ih (s+(t:ℝ)/2) (t/2))
    simp only [hc,he] at H
    rw [dyadicCDFDistance]
    apply H.trans_eq
    have hint := intervalIntegral.integral_add_adjacent_intervals
      (hi s (s+(t:ℝ)/2)) (hi (s+(t:ℝ)/2) (s+t))
    rw [pow_succ]
    calc
      _ = ((∫ z in s..s+(t:ℝ)/2, |α z-γ z|)+
          (∫ z in s+(t:ℝ)/2..s+t, |α z-γ z|))+
          (t:ℝ)/((2:ℝ)^n*2)*((α (s+t)-α s)+(γ (s+t)-γ s)) := by ring
      _ = _ := by rw [hint]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def cdfDistance (α γ : ℝ → ℝ) : ℝ := ∫ z in Icc (0:ℝ) 1, |α z-γ z|

theorem cdfDistance_nonneg (α γ : ℝ → ℝ) : 0 ≤ cdfDistance α γ :=
  integral_nonneg (fun _ => abs_nonneg _)

theorem cdfDistance_integrable {α γ : ℝ → ℝ} (hα : Monotone α) (hγ : Monotone γ) :
    IntegrableOn (fun z => |α z-γ z|) (Icc (0:ℝ) 1) :=
  ((MonotoneOn.integrableOn_isCompact isCompact_Icc (hα.monotoneOn _)).sub
    (MonotoneOn.integrableOn_isCompact isCompact_Icc (hγ.monotoneOn _))).abs

theorem cdfDistance_subinterval_le {α γ : ℝ → ℝ} (hα : Monotone α) (hγ : Monotone γ)
    {s : ℝ} {t : ℝ≥0} (hs : 0 ≤ s) (hst : s+t ≤ 1) :
    (∫ z in s..s+t, |α z-γ z|) ≤ cdfDistance α γ := by
  rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right t.coe_nonneg),← integral_Icc_eq_integral_Ioc]
  apply setIntegral_mono_set (cdfDistance_integrable hα hγ) (Eventually.of_forall (fun _ => abs_nonneg _))
  exact Eventually.of_forall (fun _ hx => ⟨hs.trans hx.1,hx.2.trans hst⟩)

theorem abs_sq_sub_sq_le_two {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    |a^2-b^2| ≤ 2*|a-b| := by
  calc
    _ = |a-b| *|a+b| := by rw [← abs_mul]; congr 1; ring
    _ ≤ |a-b| *(|a|+|b|) := mul_le_mul_of_nonneg_left (abs_add_le a b) (abs_nonneg _)
    _ ≤ |a-b| *2 := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    _ = _ := mul_comm _ _

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFQuantileInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def supportedCDFQuantile (α : StieltjesFunction ℝ) (t : ℝ) : ℝ :=
  sInf {x : ℝ | x ∈ Icc 0 1 ∧ t ≤ α x}

theorem supportedCDFQuantile_properties (α : StieltjesFunction ℝ)
    (hα1 : α 1=1) {t : ℝ} (ht : t ≤ 1) :
    supportedCDFQuantile α t ∈ Icc (0:ℝ) 1 ∧ t ≤ α (supportedCDFQuantile α t) := by
  let S : Set ℝ := {x | x ∈ Icc 0 1 ∧ t ≤ α x}
  have hn : S.Nonempty := ⟨1,⟨⟨zero_le_one,le_rfl⟩,by simpa only [hα1] using ht⟩⟩
  have hb : BddBelow S := ⟨0,fun x hx => hx.1.1⟩
  have hq : supportedCDFQuantile α t ∈ Icc (0:ℝ) 1 :=
    ⟨le_csInf hn (fun x hx => hx.1.1),csInf_le hb ⟨⟨zero_le_one,le_rfl⟩,by simpa only [hα1] using ht⟩⟩
  refine ⟨hq,?_⟩
  rw [← α.iInf_Ioi_eq (supportedCDFQuantile α t)]
  apply le_ciInf
  intro x
  obtain ⟨y,hy,hyx⟩ := exists_lt_of_csInf_lt hn x.2
  exact hy.2.trans (α.mono hyx.le)

theorem supportedCDFQuantile_le_iff (α : StieltjesFunction ℝ) (hα1 : α 1=1)
    {t x : ℝ} (ht : t ≤ 1) (hx : x ∈ Icc (0:ℝ) 1) :
    supportedCDFQuantile α t ≤ x ↔ t ≤ α x := by
  constructor
  · intro h
    exact (supportedCDFQuantile_properties α hα1 ht).2.trans (α.mono h)
  · intro h
    exact csInf_le ⟨0,fun _ hy => hy.1.1⟩ ⟨hx,h⟩

theorem supportedCDFQuantile_monotoneOn (α : StieltjesFunction ℝ) (hα1 : α 1=1) :
    MonotoneOn (supportedCDFQuantile α) (Iic 1) := by
  intro a ha b hb hab
  apply (supportedCDFQuantile_le_iff α hα1 ha
    (supportedCDFQuantile_properties α hα1 hb).1).mpr
  exact hab.trans (supportedCDFQuantile_properties α hα1 hb).2

def uniformCDFQuantiles (k : ℕ) (α : StieltjesFunction ℝ) (j : Fin (k+1)) : ℝ :=
  supportedCDFQuantile α (((j.val:ℝ)+1)/((k+1:ℕ):ℝ))

theorem uniformCDFQuantiles_admissible (k : ℕ) (α : StieltjesFunction ℝ) (hα1 : α 1=1) :
    uniformCDFQuantiles k α ∈ admissibleQuantiles k := by
  have ht (j : Fin (k+1)) : ((j.val:ℝ)+1)/((k+1:ℕ):ℝ) ≤ 1 := by
    apply (div_le_one (by positivity : (0:ℝ)<(k+1:ℕ))).mpr
    exact_mod_cast j.isLt
  constructor
  · intro i j hij
    exact supportedCDFQuantile_monotoneOn α hα1 (ht i) (ht j)
      (div_le_div_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hij 1) (by positivity))
  · intro j
    exact (supportedCDFQuantile_properties α hα1 (ht j)).1

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFUniformQuantiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem fin_sum_below {r n : ℕ} (hr : r ≤ n) (a : ℝ) :
    (∑ j : Fin n, if j.val < r then a else 0)=(r:ℝ)*a := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j < r then a else 0) n,← Finset.sum_filter]
  have he : (Finset.range n).filter (fun j => j < r)=Finset.range r := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  rw [he,Finset.sum_const,Finset.card_range,nsmul_eq_mul]

theorem quantileCDF_uniformCDFQuantiles_error (k : ℕ) (α : StieltjesFunction ℝ)
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hα1 : α 1=1) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    |quantileCDF k (uniformCDFQuantiles k α) x-α x| ≤ ((k+1:ℕ):ℝ)⁻¹ := by
  have hN : (0:ℝ)<(k+1:ℕ) := by positivity
  have ht (j : Fin (k+1)) : ((j.val:ℝ)+1)/((k+1:ℕ):ℝ) ≤ 1 := by
    apply (div_le_one hN).mpr
    exact_mod_cast j.isLt
  let a : ℝ := ((k+1:ℕ):ℝ)*α x
  have ha : 0 ≤ a := mul_nonneg hN.le (hα x).1
  have hfloor : ⌊a⌋₊ ≤ k+1 := by
    have H := (Nat.floor_le ha).trans (mul_le_of_le_one_right hN.le (hα x).2)
    exact_mod_cast H
  have he (j : Fin (k+1)) : uniformCDFQuantiles k α j ≤ x ↔ j.val < ⌊a⌋₊ := by
    rw [uniformCDFQuantiles,supportedCDFQuantile_le_iff α hα1 (ht j) hx,div_le_iff₀ hN]
    constructor
    · intro h
      have H : (j.val+1:ℕ) ≤ ⌊a⌋₊ := Nat.le_floor (by dsimp [a]; push_cast at h ⊢; nlinarith)
      omega
    · intro h
      have H : (j.val:ℝ)+1 ≤ (⌊a⌋₊:ℝ) := by exact_mod_cast h
      have H' := H.trans (Nat.floor_le ha)
      dsimp [a] at H'
      nlinarith
  rw [quantileCDF_formula]
  simp_rw [he]
  rw [fin_sum_below hfloor]
  change |(⌊a⌋₊:ℝ)/((k+1:ℕ):ℝ)-α x| ≤ ((k+1:ℕ):ℝ)⁻¹
  have H : (⌊a⌋₊:ℝ)/((k+1:ℕ):ℝ) ≤ α x := by
    apply (div_le_iff₀ hN).mpr
    simpa only [a,mul_comm] using Nat.floor_le ha
  rw [abs_of_nonpos (sub_nonpos.mpr H),neg_sub]
  have ee : α x-(⌊a⌋₊:ℝ)/((k+1:ℕ):ℝ)=(a-(⌊a⌋₊:ℝ))/((k+1:ℕ):ℝ) := by
    dsimp [a]
    field_simp
  rw [ee,inv_eq_one_div]
  apply div_le_div_of_nonneg_right _ hN.le
  linarith [Nat.lt_floor_add_one a]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarAverageCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def scalarStepLinear (v : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ ℝ+v • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem scalarStepLinear_apply (v : ℝ) (z : ℝ × ℝ) :
    scalarStepLinear v z=z.1+v*z.2 := rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_FinitePenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def finiteClockPenalty (n : ℕ) (m a : Fin n → ℝ) : ℝ :=
  ∑ i, m i*((∑ j, if j < i then a j else 0)+a i)^2-
    ∑ i, m i*(∑ j, if j < i then a j else 0)^2

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileScalarOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem blockDimension_oneSite (k : ℕ) : blockDimension 0 1 k=k+1 := by simp [blockDimension]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFPartitionRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def timeGridCoefficients (n : ℕ) (β : ℝ) (q : Fin (n+1) → ℝ) (i : Fin n) : ℝ :=
  β*Real.sqrt (q i.succ-q i.castSucc)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_PartitionOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def gridPrefix (a b : ℕ) (q : Fin (a+b+1) → ℝ) (i : Fin (a+1)) : ℝ :=
  q ⟨i.1, by omega⟩
def gridSuffix (a b : ℕ) (q : Fin (a+b+1) → ℝ) (i : Fin (b+1)) : ℝ :=
  q ⟨a+i.1, by omega⟩

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileCDFOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem quantileMass_bounds (k : ℕ) (i : Fin (k+1)) :
    quantileMass k i ∈ Icc (0:ℝ) 1 := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · apply (div_le_one (by positivity : (0:ℝ)<(k+1:ℕ))).mpr
    exact_mod_cast i.isLt.le

theorem monotone_snoc_one {n : ℕ} (q : Fin (n+1) → ℝ) (hq : Monotone q)
    (h1 : q (Fin.last n) ≤ 1) : Monotone (Fin.snoc q (1:ℝ)) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using h1
  · simpa only [← Fin.castSucc_succ,Fin.snoc_castSucc] using hq (Fin.castSucc_le_succ j)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFOverlapConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def scalarOverlapModulus (β D h : ℝ) : ℝ :=
  (4*scalarTimeMassConstant β+2*scalarTimeMassConstantK β 3)*D/h+
    12*h+2*(Real.exp (2*(scalarTimeMassConstant β*D))-1)

theorem scalarOverlapModulus_tendsto (β h : ℝ) {D : ℕ → ℝ}
    (hD : Tendsto D atTop (𝓝 0)) :
    Tendsto (fun n => scalarOverlapModulus β (D n) h) atTop (𝓝 (12*h)) := by
  have hc : Continuous (fun D : ℝ => scalarOverlapModulus β D h) := by
    unfold scalarOverlapModulus
    fun_prop
  simpa only [scalarOverlapModulus,mul_zero,zero_div,Real.exp_zero,sub_self,
    add_zero,zero_add,Function.comp_def] using hc.continuousAt.tendsto.comp hD

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_SmoothedObservable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def scalarWindow (g : ℝ → ℝ) (h x : ℝ) : ℝ :=
  (boundedPrimitive g (x+h)-boundedPrimitive g x)/h

def scalarWindowDerivative (g : ℝ → ℝ) (h x : ℝ) : ℝ := (g (x+h)-g x)/h

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_AppendTimeGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def appendTimeGrid (a b : ℕ) (q : Fin (a+1) → ℝ) (p : Fin (b+1) → ℝ) :
    Fin (a+b+1) → ℝ := Fin.append (m:=a) (n:=b+1) (fun i : Fin a => q i.castSucc) p

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarTentGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Set
namespace SK.Analytic

def scalarTentVector (n : ℕ) (v : Fin n → ℝ) (l r s : Fin (n+1)) (h : ℝ) (i : Fin n) : ℝ :=
  (2*scalarPrefixVector n v r i-scalarPrefixVector n v l i-scalarPrefixVector n v s i)/h

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarLocalTentMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def scalarTentAtomMass (n : ℕ) (m : Fin n → ℝ) (l s : Fin (n+1)) : ℝ :=
  ∑ j∈Finset.univ.filter (fun j : Fin (n+1) => l < j ∧ j < s), hierarchyAtom n m 1 j

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarHessianFloor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def scalarSusceptibilityFloor (T A : ℝ) : ℝ :=
  1/(2*(Real.cosh (1+2*A^2+4*T+8*T^2))^2)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFJointSusceptibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def conditionalSusceptibilityLipschitz : ℝ≥0 := susceptibilityLipschitzConstant+2*Real.toNNReal (Real.exp 2)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_FourBlockMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Set
namespace SK.Analytic

def narrowTentError (μ B R ω : ℝ) : ℝ := 6*R^2+2*μ*B*ω+(B*ω)^2+B^2*ω

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowTimeQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def narrowCDFMean (β : ℝ) (α : ℝ → ℝ) (r h θ : ℝ) : ℝ := β^2*(θ/h)*(∫ x in r..r+h,α x)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleCDFTrial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def tripleTimeCommonError (β K r : ℝ) : ℝ :=
  2*(2*β^2*K+(2*β^2)^2)*((susceptibilityLipschitzConstant:ℝ)+2*Real.exp 2)*
    Real.sqrt (2*(β^2*r)+4*(β^2*r)^2)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowCoefficientBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def narrowCDFErrorConstant (β : ℝ) : ℝ := 10*β^4+3*β^2

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFJointLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def scalarJointLossConstant (β a : ℝ) : ℝ :=
  β^4*a*(scalarSusceptibilityFloor (β^2) (1+2*β^2+4*(β^2)^2))^3/2

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowScaleAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def narrowExpansionDenominator (β : ℝ) : ℝ := 1+24*β^2+288*β^4

def narrowExpansionErrorConstant (β : ℝ) : ℝ :=
  (12*(susceptibilityLipschitzConstant:ℝ)+64)*(narrowExpansionDenominator β)^2

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

def strictQuantile (k : ℕ) (j : Fin (k+1)) : ℝ := ((j.val:ℝ)+1)/((k:ℝ)+2)

def regularizeQuantile (k : ℕ) (Q : Fin (k+1) → ℝ) (ε : ℝ) : Fin (k+1) → ℝ :=
  (1-ε) • Q+ε • strictQuantile k

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

def unitCDF (q x : ℝ) : ℝ := if q ≤ x then 1 else 0

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFMassSegment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def cdfMassSegment (α γ : ℝ → ℝ) (θ s : ℝ) : ℝ := α s+θ*(γ s-α s)

theorem cdfMassSegment_eq (α γ : ℝ → ℝ) (θ s : ℝ) :
    cdfMassSegment α γ θ s=(1-θ)*α s+θ*γ s := by unfold cdfMassSegment; ring

@[simp] theorem cdfMassSegment_zero (α γ : ℝ → ℝ) : cdfMassSegment α γ 0=α := by
  funext s
  simp [cdfMassSegment]

def cdfMassSegmentStieltjes (α γ : StieltjesFunction ℝ) (θ : ℝ) (hθ : θ∈Icc (0:ℝ) 1) :
    StieltjesFunction ℝ where
  toFun := cdfMassSegment α γ θ
  mono' := by
    intro s t hst
    rw [cdfMassSegment_eq,cdfMassSegment_eq]
    exact add_le_add (mul_le_mul_of_nonneg_left (α.mono hst) (sub_nonneg.mpr hθ.2))
      (mul_le_mul_of_nonneg_left (γ.mono hst) hθ.1)
  right_continuous' := by
    intro s
    exact (α.right_continuous s).add (((γ.right_continuous s).sub (α.right_continuous s)).const_mul θ)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileWeakCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

def quantileProbability (k : ℕ) (Q : Fin (k+1) → ℝ) : ProbabilityMeasure ℝ :=
  ⟨quantileAtomLaw k Q,quantileAtomLaw_probability k Q⟩

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFOptimality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def pointCDF (q : ℝ) : StieltjesFunction ℝ := cdf (Measure.dirac q)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def gaussianPair : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)
instance gaussianPair_probability : IsProbabilityMeasure gaussianPair := by
  unfold gaussianPair; infer_instance

def gaussianMix (a b : ℝ) (p : ℝ × ℝ) : ℝ := a*p.1+b*p.2

def gaussianMixCLM (a b : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ ℝ+b • ContinuousLinearMap.snd ℝ ℝ ℝ

def gaussianRotate (θ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (gaussianMix (Real.cos θ) (Real.sin θ) p,
    gaussianMix (-Real.sin θ) (Real.cos θ) p)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianAngle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology Interval
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def gaussianAngle (f g : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ p, f p.1*g (gaussianMix (Real.cos θ) (Real.sin θ) p) ∂gaussianPair

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFHeatPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def gaussianHeat (v : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z, f (x+v*z) ∂gaussianReal 0 1

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_FiniteRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

def finiteRateConstant (β : ℝ) : ℝ :=
  (β^2/4)*(60+6*(3/β^2)+2*(3/β^2)^2)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_PairBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def pairBlockVector (shared : Bool) (v : ℝ) (u : Fin 2) : ℝ × ℝ :=
  if shared then if u=0 then (v,v) else 0 else if u=0 then (v,0) else (0,v)

def splitPairMass {n : ℕ} (a : ℕ) (m : Fin n → ℝ) (j : Fin n) : ℝ := if j.val<a then m j/2 else m j

def splitPairVector {n : ℕ} (a : ℕ) (v : Fin n → ℝ) (j : Fin n) : Fin 2 → ℝ × ℝ :=
  pairBlockVector (decide (j.val<a)) (v j)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_PairFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def pairMatrix (t q : ℝ) (i j : Fin 2) : ℝ := if i=j then t else q

def pairFactor (shared : Bool) (c : ℝ) (u i : Fin 2) : ℝ :=
  if i=0 then (pairBlockVector shared c u).1 else (pairBlockVector shared c u).2

def splitPairFactor {n : ℕ} (a : ℕ) (c : Fin n → ℝ) (j : Fin n) : Fin 2 → Fin 2 → ℝ :=
  pairFactor (decide (j.val<a)) (c j)

def pairMultiplier : Fin 2 → Fin 2 → ℝ := pairMatrix 0 (1/2)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_OverlapCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def codeOverlap (n : ℕ) (c : Fin (n+1)) : ℝ := (2*(c.val:ℝ)-(n:ℝ))/(n:ℝ)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_Crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def lastCrossing (f : ℕ → ℝ) (r : ℝ) (u : ℕ) : ℕ :=
  Nat.findGreatest (fun k => f k ≤ r) u

def firstCrossing (f : ℕ → ℝ) (r : ℝ) (m : ℕ) : ℕ :=
  if h : ∃ k, k ≤ m ∧ f k ≤ r then Nat.find h else 0

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_GridThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical MeasureTheory Set
namespace SK.Analytic

def thresholdGrid (n : ℕ) (a ρ : ℝ) (i : Fin n) : ℝ := a+ρ*(i:ℕ)/(n:ℝ)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_PredictableGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical MeasureTheory Set
namespace SK.Analytic

def gridThresholds (n p : ℕ) (t ρ : ℝ) (z : Fin p → Fin n) (j : ℕ) : ℝ :=
  if h : j<p then thresholdGrid n (t+4*j*ρ) ρ (z ⟨j,h⟩) else t+4*j*ρ

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_GreedyNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory Filter Set
namespace SK.Analytic

def greedySlack (t ρ : ℝ) : ℝ := (3*t/4)*ρ^19+2*ρ^100+ρ^20+3*ρ^10000

def levelLogScale (n : ℕ) : ℝ := (n:ℝ)^kappa
def levelRho (n : ℕ) : ℝ := (n:ℝ)^(-kappa)

def greedyBlockCount (B : ℕ) (t : ℝ) (n : ℕ) : ℕ := ⌊(t/(8*B))*levelLogScale n⌋₊

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_CoverageSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def coveragePrefix (f : ℝ → ℝ) : ℕ → ℝ
  | 0 => 0
  | j+1 => coveragePrefix f j+f (coveragePrefix f j+5)+2

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarOneAtomMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

def scalarGaussianOverlap (v : ℝ) : ℝ :=
  ∫ y, (scalarMagnetization (v*y))^2 ∂gaussianReal 0 1

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarInstability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

def oneAtomTrial (β v : ℝ) : ℝ := scalarGaussianValue v+(β^2/4)*(1-v^2/β^2)^2

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_FiniteScalarGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

def quantileFirstMoment (k : ℕ) (Q : Fin (k+1) → ℝ) : ℝ :=
  ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*Q j

def quantileSecondMoment (k : ℕ) (Q : Fin (k+1) → ℝ) : ℝ :=
  ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Q j)^2

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_BankNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory Filter Set
namespace SK.Analytic

def scheduledBankSize (c : ℕ → ℝ) (B n : ℕ) {p : ℕ} (j : Fin p) : ℕ :=
  ⌈Real.exp ((c (j.val%B)+1)*levelLogScale n)⌉₊

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_Uniformization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def clockWeight (a : ℝ) (k : ℕ) : ℝ := Real.exp (-a)*a^k/(k.factorial:ℝ)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_IdentityDynamics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def bankEndpointError (n : ℕ) : ℝ :=
  4*(9*Real.exp (-2*levelLogScale n)+(n:ℝ)*Real.exp (-levelLogScale n))

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_ForbiddenMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def forbiddenEndpointError (n : ℕ) : ℝ := Real.exp (-3*levelLogScale n)+48*Real.exp (-8*levelLogScale n)

end SK.Analytic

end
end

end OAI
end


