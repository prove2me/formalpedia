-- Prove2me | Definitions.Def_OAIQWPR000
-- name    : OAIQWPR000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T16:31:26.320654+00:00
-- url     : https://prove2.me/theorems/04acb85c-1ea3-41b2-bda7-f501c7e81258
-- title:
--   OpenAI posterior replicas split: definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof of the posterior-replica information bounds and the memory lower bound for exact Gaussian regression (`OAI.PosteriorReplicas.source_main`). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Probability/PosteriorReplicas` (OpenAI, *Posterior replicas and conditional information in Gaussian regression*, OpenAI Math Release, September 27, 2026, result family 140, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. Among them are:
--   - the seeded learners of the memory bound (`PosteriorRegression.Learner`, with `Learner.Admissible`, `Learner.UniformAdmissible`, `Learner.uniformSuccess`), the statement `PosteriorRegression.FixedQuadraticMemory`, and the coin realization of a completed kernel learner (`CompletedKernelLearner.Realization`, `CompletedKernelLearner.uniformSuccess`);
--   - the equal-label laws: the space `EqualSpace` of triples (rows, labels, tuple), the reference law `equalReference`, the replica law `replicaLaw` with its density `replicaDensity`, and the base measures `leftBaseMeasure` and `rightBaseMeasure`;
--   - the density envelopes `expectedDensity`, `tupleDistance`, `ellipsoidMass` and `binEnvelope`;
--   - the auxiliary projection (`auxLaw`, `observableRows`, `observe`, `observableLikelihood`, `observableLog`) and the comparison quantities `normalizedRatio`, `projectionGramRatio`, `binMeanBound`, `comparisonEnvelope`, `comparisonCost` and `wishartMoment`;
--   - Gaussian and geometric helpers such as `gramVolume`, `randomComplement`, `rowMix` and `pairingColumns`.
--
--   The bundle also contains the lemmas those definitions use in their bodies, and the measurability lemmas tagged for `fun_prop` that come with them.
--
--   The definitions of the published statement (`sphereLaw`, `gaussianRows`, `labels`, `signalMessageLaw`, `sideLaw`, `conditionalInformation`, `projectedDensity`, the eight component propositions and the rest) are not repeated: the bundle imports them from the published bundle `Def_PosteriorReplicas`. It imports no other bundle. A small compatibility section declares, inside namespace `OAI`, `Measurable.of_eval`, the newer Mathlib name for `measurable_pi_lambda`.
--
--   Modules: `Gaussian/ConstrainedGaussian.lean`, `Gaussian/ConstrainedNoise.lean`, `Gaussian/GaussianDensity.lean`, `Gaussian/GaussianFiber.lean`, `Gaussian/GaussianGramMoment.lean`, `Gaussian/GaussianLogMoment.lean`, `Gaussian/GaussianPolar.lean`, `Gaussian/GaussianRowMix.lean`, `Gaussian/GaussianWishart.lean`, `Gaussian/GramTransform.lean`, `Gaussian/MatrixNoise.lean`, `Gaussian/RandomComplement.lean`, `Geometry/BallJacobian.lean`, `Geometry/BaseContinuity.lean`, `Geometry/BaseFunProp.lean`, `Geometry/BaseGeometry.lean`, `Geometry/DensityBinEnvelope.lean`, `Geometry/DensityBinsGeometry.lean`, `Geometry/FrameTubes.lean`, `Geometry/LabelConvolution.lean`, `Geometry/SphereDensity.lean`, `Geometry/TupleMoments.lean`, `Information/BinCutoff.lean`, `Information/ConditionalPiKL.lean`, `Information/GraphKL.lean`, `Information/HaarInformationEq.lean`, `Information/NormalizedLikelihood.lean`, `Information/ObservableLikelihood.lean`, `Information/ParametricKernel.lean`, `Information/PiKL.lean`, `Information/ReplicaInformation.lean`, `Information/ReplicaLoss.lean`, `Information/StateExperiment.lean`, `Information/StateSide.lean`, `Kernels/DensityRatio.lean`, `Kernels/KernelPi.lean`, `Kernels/PosteriorExperiment.lean`, `Kernels/PosteriorKernel.lean`, `Kernels/ReplicaGaussianMarginals.lean`, `Kernels/ReplicaMeasure.lean`, `Learners/CompletedKernelLaw.lean`, `Learners/CompletedKernelLearner.lean`, `Learners/KernelLearnerBridge.lean`, `Learners/KernelSuccess.lean`, `Learners/LearnerModelBridge.lean`, `Measures/BaseDisintegration.lean`, `Measures/DensityDifferentiation.lean`, `Measures/EqualApproximation.lean`, `Measures/EqualBaseMeasures.lean`, `Measures/EqualRightMeasure.lean`, `Measures/EuclideanLabels.lean`, `Measures/GaussianDifferentiation.lean`, `Regression/Fubini.lean`, `Regression/FrostmanGeometry.lean`, `Regression/GramDistances.lean`, `Regression/GramFactorization.lean`, `Regression/LearnerBasics.lean`, `Regression/ProjectionBlocks.lean`, `Regression/ProjectionCoupling.lean`, `Regression/ReplicaMoments.lean`, `Regression/SmoothingMoments.lean`, `Regression/SphereBounds.lean`, `Regression/SphereGeometry.lean`, `Regression/StreamCaps.lean`, `Regression/StreamIntegrals.lean`, `Regression/StreamSlices.lean`, `Regression/SupportVolume.lean`.
--
--   The theorems of the development that the definitions do not need are proved in the 20 solutions of this split. Nineteen of them prove the published intermediate statements: the eight components `OAI.PosteriorReplicas.equalLabelMeasureIdentity`, `OAI.PosteriorReplicas.equalLabelVersions`, `OAI.PosteriorReplicas.gaussianReplicaBlock`, `OAI.PosteriorReplicas.distanceReplicaBlock`, `OAI.PosteriorReplicas.haarReplicaBlock`, `OAI.PosteriorReplicas.syntheticReplicaBlock`, `OAI.PosteriorReplicas.incidenceReplicaBlock` and `OAI.PosteriorRegression.kernel_subquadratic_memory`, and eleven lemmas behind them. The last one proves `OAI.PosteriorReplicas.source_main` from the eight components. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Posterior replicas and conditional information in Gaussian regression, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Posterior-replicas-and-conditional-information-in-Gaussian-regression-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/PosteriorReplicas at commit adc7f12

import Mathlib
import Definitions.Def_PosteriorReplicas

section
-- module Solutions.OAIQW_PosteriorReplicas.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_GramFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
section GramFactorization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι : Type*} [Fintype ι]

variable (n : ℕ)
def gsUpper (v : Fin n → E) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  (if i = j then 1 else 0) +
    if i < j then ⟪gramSchmidt ℝ v i, v j⟫ / ‖gramSchmidt ℝ v i‖ ^ 2 else 0

end GramFactorization

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_FrostmanGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
section FrostmanGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def HasLocalMassBound (ν : Measure E) (a : ℝ) : Prop :=
  ∀ t ∈ ν.support, ∀ r : ℝ, 0 < r →
    ν (Metric.closedBall t r) ≤ ENNReal.ofReal (r ^ a)

end FrostmanGeometry

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_GramDistances
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
section GramDistances
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

variable [MeasurableSpace E] [BorelSpace E]
lemma measurable_gramSchmidt (j : Fin n) :
    Measurable (fun v : Fin n → E => gramSchmidt ℝ v j) := by
  refine (wellFounded_lt : WellFounded ((· < ·) : Fin n → Fin n → Prop)).induction
    (C := fun j : Fin n => Measurable (fun v : Fin n → E => gramSchmidt ℝ v j)) j ?_
  intro j ih
  have heq : (fun v : Fin n → E => gramSchmidt ℝ v j) =
      fun v => v j - ∑ i ∈ Finset.Iio j,
        (⟪gramSchmidt ℝ v i, v j⟫ / ‖gramSchmidt ℝ v i‖ ^ 2) • gramSchmidt ℝ v i := by
    ext v
    rw [gramSchmidt_def]
    simp only [Submodule.starProjection_singleton]
    rfl
  rw [heq]
  apply (measurable_pi_apply j).sub
  apply Finset.measurable_sum
  intro i hi
  have hi' := ih i (Finset.mem_Iio.mp hi)
  exact ((hi'.inner (measurable_pi_apply j)).div (hi'.norm.pow_const 2)).smul hi'
end GramDistances

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_ReplicaMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
section ReplicaMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def replicaWeight (m : ℕ) (p : E) {n : ℕ} (v : Fin n → E) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal ((‖gramSchmidt ℝ (fun j => v j - p) i‖)⁻¹ ^ m)

def replicaConstant (ν : Measure E) (a : ℝ) (m : ℕ) : ℝ≥0∞ :=
  ν Set.univ + ENNReal.ofReal ((3 : ℝ) ^ Module.finrank ℝ E * (4 : ℝ) ^ a) *
    (2 : ℝ≥0∞) ^ (m+1)

end ReplicaMoments

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_SmoothingMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
section SmoothingMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def projectionSmoothing (ν : Measure E) (φ : ℝ → ℝ≥0∞) (m : ℕ)
    (z : (Fin m → E) × (Fin m → ℝ)) : ℝ≥0∞ :=
  ∫⁻ t, ∏ j, φ (z.2 j - ⟪t, z.1 j⟫) ∂ν

end SmoothingMoments

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_ProjectionCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
section ProjectionCoupling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def matrixLabelReference (m : ℕ) : Measure ((Fin m → E) × (Fin m → ℝ)) :=
  (Measure.pi (fun _ => stdGaussian E)).prod volume

def projectionLaw (ν : Measure E) (m : ℕ) : Measure ((Fin m → E) × (Fin m → ℝ)) :=
  ((Measure.pi (fun _ => stdGaussian E)).prod ν).map
    (fun z => (z.1, fun j => ⟪z.2, z.1 j⟫))

def gaussianCoupling (ν : Measure E) (m : ℕ) :
    Measure ((Fin m → E) × (E × (Fin m → ℝ))) :=
  (Measure.pi (fun _ => stdGaussian E)).prod
    (ν.prod (Measure.pi (fun _ => gaussianReal 0 1)))

def noisyObservation (m : ℕ) (δ : ℝ)
    (z : (Fin m → E) × (E × (Fin m → ℝ))) : (Fin m → E) × (Fin m → ℝ) :=
  (z.1, fun j => ⟪z.2.1, z.1 j⟫ + δ * z.2.2 j)

end ProjectionCoupling

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_SupportVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
section SupportVolume
open scoped Pointwise

def coordinateNorm {m : ℕ} (y : Fin m → ℝ) : ℝ := ‖WithLp.toLp 2 y‖

@[fun_prop] lemma continuous_coordinateNorm {m : ℕ} :
    Continuous (coordinateNorm (m := m)) := by
  unfold coordinateNorm
  fun_prop

def coordinateBall (m : ℕ) (r : ℝ) : Set (Fin m → ℝ) :=
  {y | coordinateNorm y ≤ r}

section Rows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def rowOperator {m : ℕ} (A : Fin m → E) : E →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j => innerSL ℝ (A j)))

def netProjectionSupport (s : Finset E) (m : ℕ) :
    Set ((Fin m → E) × (Fin m → ℝ)) :=
  ⋃ u ∈ s, {z | coordinateNorm z.2 ≤ 2 * coordinateNorm (fun j => ⟪u, z.1 j⟫)}

end Rows

end SupportVolume

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_SphereBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
section SphereBounds
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def unitBallLaw : Measure E :=
  ((volume : Measure E) (Metric.ball 0 1))⁻¹ • volume.restrict (Metric.closedBall 0 1)

def sphereLaw : Measure (Metric.sphere (0 : E) 1) :=
  let σ := (volume : Measure E).toSphere
  (σ Set.univ)⁻¹ • σ

instance unitBallLaw_probability : IsProbabilityMeasure (unitBallLaw : Measure E) := by
  constructor
  rw [unitBallLaw, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
    Measure.addHaar_closedBall _ _ (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [one_pow, ENNReal.ofReal_one, one_mul]
  exact ENNReal.inv_mul_cancel (Metric.measure_ball_pos volume 0 zero_lt_one).ne'
    measure_ball_lt_top.ne

instance sphereLaw_probability [Nontrivial E] : IsProbabilityMeasure (sphereLaw (E := E)) := by
  constructor
  rw [sphereLaw, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.inv_mul_cancel _ (measure_ne_top _ _)
  rw [Measure.toSphere_apply_univ]
  exact mul_ne_zero (by exact_mod_cast (Module.finrank_pos (R := ℝ) (M := E)).ne')
    (Metric.measure_ball_pos volume 0 zero_lt_one).ne'

end SphereBounds

open scoped Pointwise

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_SphereGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
open scoped Pointwise
section MoreSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def ambientSphereLaw : Measure E := (sphereLaw (E := E)).map Subtype.val

instance ambientSphereLaw_probability [Nontrivial E] : IsProbabilityMeasure (ambientSphereLaw (E := E)) := by
  unfold ambientSphereLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

def sphereIsometry (e : E ≃ₗᵢ[ℝ] E) : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1 :=
  e.toHomeomorph.subtype (fun x => by
    simp only [mem_sphere_zero_iff_norm]
    change ‖x‖ = 1 ↔ ‖e x‖ = 1
    rw [e.norm_map])

end MoreSphere

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_Fubini
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
open scoped Pointwise

instance sampleLaw_probability (d T : ℕ) : IsProbabilityMeasure (sampleLaw d T) := by
  unfold sampleLaw
  infer_instance
instance uniformSphere_probability (d : ℕ) [NeZero d] : IsProbabilityMeasure (uniformSphere d) := by
  change IsProbabilityMeasure (sphereLaw (E := Vector d))
  infer_instance

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_LearnerBasics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression

structure Learner (d M T : ℕ) (Ω : Type u) where
  initialChoice : Ω → Bool × State M
  transition : ℕ → Ω → State M → (Vector d × ℝ) → Bool × State M
  output : ℕ → Ω → State M → UnitSphere d

namespace Learner

def start {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω) (ω : Ω) :
    RunStatus M :=
  let a := L.initialChoice ω
  if a.1 then .inr (0, a.2) else .inl a.2

def run {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s : UnitSphere d) (ω : Ω) (x : Samples d T) : ℕ → RunStatus M
  | 0 => L.start ω
  | n + 1 =>
    match L.run s ω x n with
    | .inr done => .inr done
    | .inl state =>
      if hn : n < T then
        let row := x ⟨n, hn⟩
        let a := L.transition (n + 1) ω state (row, ⟪row, s.val⟫)
        if a.1 then .inr (n + 1, a.2) else .inl a.2
      else .inl state

def terminal {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s : UnitSphere d) (ω : Ω) (x : Samples d T) : ℕ × State M :=
  match L.run s ω x T with
  | .inl state => (T, state)
  | .inr done => done

def estimate {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s : UnitSphere d) (ω : Ω) (x : Samples d T) : UnitSphere d :=
  let a := L.terminal s ω x
  L.output a.1 ω a.2

structure Admissible {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) : Prop where
  initialChoice : AEMeasurable L.initialChoice ρ
  transition : ∀ t a, AEMeasurable (fun z : Ω × (Vector d × ℝ) =>
    L.transition t z.1 a z.2) (ρ.prod (observationReference d))
  output : ∀ t a, AEMeasurable (fun ω => L.output t ω a) ρ
  fixed_experiment : ∀ s, AEMeasurable (fun z : Ω × Samples d T =>
    L.estimate s z.1 z.2) (ρ.prod (sampleLaw d T))
  uniform_experiment : AEMeasurable
    (fun z : UnitSphere d × (Ω × Samples d T) => L.estimate z.1 z.2.1 z.2.2)
    ((uniformSphere d).prod (ρ.prod (sampleLaw d T)))

def uniformSuccess {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) (ε : ℝ) : ℝ≥0∞ :=
  ((uniformSphere d).prod (ρ.prod (sampleLaw d T)))
    {z | angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}

end Learner

def FixedQuadraticMemory : Prop :=
  ∀ A₀ : ℝ, 0 < A₀ → ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ,
    ∀ d : ℕ, d₀ ≤ d → ∀ M T : ℕ, (M : ℝ) ≤ A₀ * (d : ℝ) ^ 2 →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : Learner d M T Ω, L.Admissible ρ →
    (2 / 3 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε →
    c * (d : ℝ) * Real.log (1 / ε) ≤ (T : ℝ)

open scoped Topology

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_ProjectionBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
open scoped Pointwise
section Block
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def PolynomialMass (ν : Measure E) (a : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ z : E, ∀ r : ℝ, 0 < r → ν (Metric.closedBall z r) ≤ C * ENNReal.ofReal (r^a)

def localNormalize (ν : Measure E) (a : ℕ) (C : ℝ≥0∞) (z : E) (r : ℝ) : Measure E :=
  (C * ENNReal.ofReal (r^a))⁻¹ • (ν.restrict (Metric.closedBall z r)).map (fun x => r⁻¹ • (x-z))

def blockValue {J : Type*} [Fintype J] {m : ℕ} (h : J → E → ℝ≥0∞)
    (φ : ((Fin m → E) × (Fin m → ℝ)) → J) (s : E) : ℝ≥0∞ :=
  ∫⁻ A, h (φ (A, fun j => ⟪s,A j⟫)) s ∂Measure.pi (fun _ : Fin m => stdGaussian E)

end Block

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_StreamIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
open scoped Pointwise
section StreamAux
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

def streamRoute (δ : ℕ → J → (E × ℝ) → J) (n : ℕ) :
    (k : ℕ) → J → ((Fin k → E) × (Fin k → ℝ)) → J
  | 0, j, _ => j
  | k+1, j, x => streamRoute δ (n+1) k (δ (n+1) j (x.1 0, x.2 0)) (Fin.tail x.1, Fin.tail x.2)

def continuation (δ : ℕ → J → (E × ℝ) → J) (w : ℕ → J → E → ℝ≥0∞)
    (n : ℕ) : ℕ → J → E → ℝ≥0∞
  | 0, j, s => w n j s
  | k+1, j, s => ∫⁻ x, continuation δ w (n+1) k (δ (n+1) j (x, ⟪s,x⟫)) s ∂stdGaussian E

def streamFactor (q : ℕ) : ℝ≥0∞ :=
  (32768 : ℝ≥0∞)^Module.finrank ℝ E * (Fintype.card J : ℝ≥0∞)^(1/(q : ℝ))

end StreamAux

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_StreamSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
open scoped Pointwise
namespace Learner
variable {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)

def forcedRun (L : Learner d M T Ω) (s : UnitSphere d) (ω : Ω) (x : Samples d T) : ℕ → State M
  | 0 => (L.initialChoice ω).2
  | n+1 =>
    if hn : n < T then
      (L.transition (n+1) ω (L.forcedRun s ω x n) (x ⟨n,hn⟩, ⟪x ⟨n,hn⟩,s.val⟫)).2
    else L.forcedRun s ω x n

end Learner

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_StreamCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
open scoped Pointwise
section StreamCaps
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]

def capWeight (y : E) (ε : ℝ) : E → ℝ≥0∞ :=
  (Metric.closedBall y ε).indicator (fun _ => 1)

end StreamCaps

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Gaussian_GaussianFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace PosteriorReplicas

section GaussianSplitting
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def pairingLift {n : ℕ} (v : Fin n → E) (y : Fin n → ℝ) : E :=
  ∑ i, ((Matrix.gram ℝ v)⁻¹ *ᵥ y) i • v i

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[fun_prop] lemma continuous_pairingLift {n : ℕ} (v : Fin n → E) : Continuous (pairingLift v) := by
  unfold pairingLift
  fun_prop

end GaussianSplitting
end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Gaussian_GaussianDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace PosteriorReplicas

def matrixLinearEquiv {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hd : M.det ≠ 0) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
  { Matrix.toLin' M with
    invFun := Matrix.toLin' M⁻¹
    left_inv := by
      intro x
      change M⁻¹ *ᵥ (M *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd),
        Matrix.one_mulVec]
    right_inv := by
      intro x
      change M *ᵥ (M⁻¹ *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd),
        Matrix.one_mulVec] }

section PairingsDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def pairingTriangular {n : ℕ} (v : Fin n → E) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => ‖gramSchmidt ℝ v i‖) * PosteriorRegression.gsUpper n v

end PairingsDensity
end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Gaussian_ConstrainedGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace PosteriorReplicas

section Rows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def pairingsDensity {n : ℕ} (v : Fin n → E) (y : Fin n → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Real.pi) ^ (-(n : ℝ) / 2) *
    Real.exp (-‖pairingLift v y‖^2 / 2) / Real.sqrt (Matrix.gram ℝ v).det)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[fun_prop] lemma continuous_pairingsDensity
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ} (v : Fin n → E) :
    Continuous (pairingsDensity v) := by
  unfold pairingsDensity
  exact ENNReal.continuous_ofReal.comp (by fun_prop)

end Rows
end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Gaussian_MatrixNoise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
noncomputable section
namespace PosteriorReplicas

def transposeCLE (m k : ℕ) : (Fin m → Fin k → ℝ) ≃L[ℝ] (Fin k → Fin m → ℝ) :=
  ({ toFun := fun z j i => z i j
     invFun := fun z i j => z j i
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } :
        (Fin m → Fin k → ℝ) ≃ₗ[ℝ] (Fin k → Fin m → ℝ)).toContinuousLinearEquiv

@[simp] lemma transposeCLE_apply (m k : ℕ) (z : Fin m → Fin k → ℝ) :
    transposeCLE m k z = fun j i => z i j := rfl

instance matrixPiVolumeAddHaar (m k : ℕ) :
    (volume : Measure (Fin m → Fin k → ℝ)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure (fun _ : Fin m => (volume : Measure (Fin k → ℝ)))

def matrixNormal (m k : ℕ) : Measure (Fin m → Fin k → ℝ) :=
  Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1

instance instIsProbabilityMeasureForallFinForallRealMatrixNormal (m k : ℕ) : IsProbabilityMeasure (matrixNormal m k) := by
  unfold matrixNormal
  infer_instance

def noiseScale (n : ℕ) : ℝ := 1 / (n + 1)

def matrixNoiseDensity (m k n : ℕ) (z : Fin m → Fin k → ℝ) : ℝ≥0∞ :=
  ∏ i, ∏ j, gaussianPDF 0 (⟨(noiseScale n)^2, sq_nonneg _⟩ : ℝ≥0) (z i j)

@[fun_prop] lemma measurable_matrixNoiseDensity (m k n : ℕ) :
    Measurable (matrixNoiseDensity m k n) := by
  unfold matrixNoiseDensity
  fun_prop

end PosteriorReplicas

end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Gaussian_ConstrainedNoise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

section Generic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def gaussianResidualRows {m : ℕ} (v : Fin m → E) (k : ℕ) : Measure (Fin k → E) :=
  Measure.pi fun _ => (stdGaussian E).map (Submodule.span ℝ (Set.range v))ᗮ.starProjection

instance instIsProbabilityMeasureForallFinGaussianResidualRows {m : ℕ} (v : Fin m → E) (k : ℕ) : IsProbabilityMeasure (gaussianResidualRows v k) := by
  let : IsProbabilityMeasure ((stdGaussian E).map (Submodule.span ℝ (Set.range v))ᗮ.starProjection) :=
    (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  unfold gaussianResidualRows
  infer_instance

end Generic
end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Gaussian_GaussianPolar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def gaussianRadialDensity (d : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-r^2 / 2))

@[fun_prop] lemma continuous_gaussianRadialDensity (d : ℕ) :
    Continuous (gaussianRadialDensity d) :=
  ENNReal.continuous_ofReal.comp (by fun_prop)

def gaussianPolarRadius (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : Measure (Ioi (0 : ℝ)) :=
  (Measure.volumeIoiPow (Module.finrank ℝ E - 1)).withDensity
    (fun r => gaussianRadialDensity (Module.finrank ℝ E) r.1)

instance instSFiniteElemRealIoiOfNatGaussianPolarRadius : SFinite (gaussianPolarRadius E) := by
  unfold gaussianPolarRadius
  infer_instance

def normalDirection (x : E) : E := ‖x‖⁻¹ • x

@[fun_prop] lemma measurable_normalDirection : Measurable (normalDirection (E := E)) := by
  unfold normalDirection
  fun_prop

def uniformDirection (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Measure E :=
  let σ := (volume : Measure E).toSphere
  ((σ univ)⁻¹ • σ).map Subtype.val

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_BaseGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

instance matrixRealMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℝ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℝ))

instance matrixRealBorelSpace (m n : Type*) [Countable m] [Countable n] :
    BorelSpace (Matrix m n ℝ) := inferInstanceAs (BorelSpace (m → n → ℝ))

attribute [fun_prop] measurable_labels

@[fun_prop] lemma measurable_matrix_inv_real (n : ℕ) :
    Measurable (fun M : Matrix (Fin n) (Fin n) ℝ => M⁻¹) := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]
  exact continuous_id.matrix_det.measurable.inv.smul continuous_id.matrix_adjugate.measurable

@[fun_prop] lemma continuous_rowGram {d k : ℕ} : Continuous (@rowGram d k) := by
  unfold rowGram
  fun_prop

@[fun_prop] lemma measurable_liftLabel {d k : ℕ} :
    Measurable (fun z : Rows d k × Labels k => liftLabel z.1 z.2) := by
  unfold liftLabel Matrix.mulVec dotProduct
  fun_prop

@[fun_prop] lemma continuous_liftLabel {d k : ℕ} (A : Rows d k) :
    Continuous (liftLabel A) := continuous_pairingLift A

@[fun_prop] lemma measurable_kernelComponent {d k : ℕ} :
    Measurable (fun z : Rows d k × Vec d => kernelComponent z.1 z.2) := by
  unfold kernelComponent
  fun_prop

def basePoint {d k : ℕ} (base : BaseLaw) (A : Rows d k) (y : Labels k) (x : Vec d) : Vec d :=
  match base with
  | .gaussian => liftLabel A y + kernelComponent A x
  | .spherical => liftLabel A y +
      (Real.sqrt (1 - ‖liftLabel A y‖ ^ 2) / ‖kernelComponent A x‖) • kernelComponent A x

@[fun_prop] lemma measurable_basePoint {d k : ℕ} (base : BaseLaw) :
    Measurable (fun z : (Rows d k × Labels k) × Vec d => basePoint base z.1.1 z.1.2 z.2) := by
  cases base <;> unfold basePoint <;> fun_prop

lemma baseFiber_eq_map {d k : ℕ} (base : BaseLaw) (A : Rows d k) (y : Labels k) :
    baseFiber base A y = (stdGaussian (Vec d)).map (basePoint base A y) := by
  cases base <;> rfl

@[fun_prop] lemma measurable_basePoint_fixed {d k : ℕ} (base : BaseLaw)
    (A : Rows d k) (y : Labels k) : Measurable (basePoint base A y) := by
  have h := (measurable_basePoint (d := d) (k := k) base).comp
    (show Measurable (fun x : Vec d => ((A, y), x)) from measurable_const.prodMk measurable_id)
  exact h

instance instIsProbabilityMeasureVecBaseFiber {d k : ℕ} (base : BaseLaw) (A : Rows d k) (y : Labels k) :
    IsProbabilityMeasure (baseFiber base A y) := by
  rw [baseFiber_eq_map]
  exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma measurable_parametric_map {Z X Y : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [MeasurableSpace Y] (μ : Measure X) [SFinite μ] {F : Z × X → Y} (hF : Measurable F) :
    Measurable (fun z => μ.map (fun x => F (z, x))) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have he : (fun z => μ.map (fun x => F (z, x)) s) =
      (fun z => μ ((Prod.mk z) ⁻¹' (F ⁻¹' s))) := by
    funext z
    exact Measure.map_apply (hF.comp (measurable_const.prodMk measurable_id)) hs
  rw [he]
  exact measurable_measure_prodMk_left (hF hs)

@[fun_prop] lemma measurable_baseFiber {d k : ℕ} (base : BaseLaw) :
    Measurable (fun z : Rows d k × Labels k => baseFiber base z.1 z.2) := by
  simp_rw [baseFiber_eq_map]
  exact measurable_parametric_map _ (measurable_basePoint base)

def baseKernel {d k : ℕ} (base : BaseLaw) : Kernel (Rows d k × Labels k) (Vec d) where
  toFun z := baseFiber base z.1 z.2
  measurable' := measurable_baseFiber base

instance instIsMarkovKernelProdRowsLabelsVecBaseKernel {d k : ℕ} (base : BaseLaw) : IsMarkovKernel (@baseKernel d k base) where
  isProbabilityMeasure _ := by dsimp [baseKernel]; infer_instance

@[fun_prop] lemma measurable_tiltMass {d k : ℕ} (base : BaseLaw) {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) : Measurable (fun z : Rows d k × Labels k => tiltMass base f z.1 z.2) := by
  unfold tiltMass
  exact hf.lintegral_kernel (κ := baseKernel base)

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_BallJacobian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Matrix InnerProductSpace Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

section Ball
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def ballStretch (x : E) : E := (1 - ‖x‖^2) ^ (-(1 : ℝ) / 2) • x

def ballStretchDeriv (x : E) : E →L[ℝ] E :=
  (1 - ‖x‖^2) ^ (-(1 : ℝ) / 2) •
    (ContinuousLinearMap.id ℝ E +
      (1 - ‖x‖^2)⁻¹ • ((innerSL ℝ x).smulRight x))

@[fun_prop] lemma measurable_ballStretch [MeasurableSpace E] [BorelSpace E] :
    Measurable (ballStretch : E → E) := by
  unfold ballStretch
  fun_prop

end Ball
end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_SphereDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def sphericalPairingsDensity {n : ℕ} (v : Fin n → E) (y : Fin n → ℝ) : ℝ≥0∞ :=
  if ‖pairingLift v y‖ < 1 then ENNReal.ofReal
    (Real.Gamma (((Module.finrank ℝ E : ℕ) : ℝ) / 2) /
      (Real.pi ^ ((n : ℝ) / 2) * Real.Gamma ((((Module.finrank ℝ E : ℕ) : ℝ) - n) / 2)) *
        (1 - ‖pairingLift v y‖^2) ^ ((((Module.finrank ℝ E : ℕ) : ℝ) - n - 2) / 2) /
          Real.sqrt (Matrix.gram ℝ v).det) else 0

omit [FiniteDimensional ℝ E] in
@[fun_prop] lemma measurable_sphericalPairingsDensity [FiniteDimensional ℝ E]
    {n : ℕ} (v : Fin n → E) :
    Measurable (sphericalPairingsDensity v) := by
  unfold sphericalPairingsDensity
  exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) (by fun_prop) measurable_const

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Measures_BaseDisintegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

instance baseLaw_probability (base : BaseLaw) (d : ℕ) [NeZero d] :
    IsProbabilityMeasure (base.measure d) := by
  cases base
  · change IsProbabilityMeasure (PosteriorRegression.ambientSphereLaw (E := Vec d))
    infer_instance
  · change IsProbabilityMeasure (stdGaussian (Vec d))
    infer_instance

@[fun_prop] lemma measurable_baseDensity {d k : ℕ} (base : BaseLaw) :
    Measurable (fun z : Rows d k × Labels k => baseDensity base z.1 z.2) := by
  have hLI : MeasurableSet {z : Rows d k × Labels k | LinearIndependent ℝ z.1} := by
    simp_rw [← Matrix.det_gram_ne_zero_iff_linearIndependent]
    exact (measurableSet_eq_fun ((continuous_rowGram.comp continuous_fst).matrix_det.measurable)
      measurable_const).compl
  unfold baseDensity
  apply Measurable.ite hLI
  · cases base
    · exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
        (by fun_prop) measurable_const
    · fun_prop
  · exact measurable_const

@[fun_prop] lemma measurable_projectedDensity {d k : ℕ} (base : BaseLaw)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun z : Rows d k × Labels k => projectedDensity base f z.1 z.2) :=
  (measurable_baseDensity base).mul (measurable_tiltMass base hf)

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_FrameTubes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

def baseProjectionConstant (base : BaseLaw) (d k : ℕ) : ℝ :=
  match base with
  | .gaussian => (2 * Real.pi) ^ (-(k : ℝ) / 2)
  | .spherical => Real.Gamma ((d : ℝ) / 2) /
      (Real.pi ^ ((k : ℝ) / 2) * Real.Gamma (((d : ℝ) - k) / 2))

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Gaussian_GaussianGramMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric EuclideanGeometry Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def gaussianMomentConstant (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.sqrt k)⁻¹^k) *
    (1 + ENNReal.ofReal (Real.exp ((k : ℝ)/2)) * 2^(k+1))

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Gaussian_GaussianLogMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace PosteriorReplicas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def gramVolume {m : ℕ} (v : Fin m → E) : ℝ := Real.sqrt (Matrix.gram ℝ v).det

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_BaseFunProp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace PosteriorReplicas

@[fun_prop] lemma measurable_basePoint_comp {X : Type*} [MeasurableSpace X]
    {d k : ℕ} (base : BaseLaw) {A : X → Rows d k} {y : X → Labels k} {x : X → Vec d}
    (hA : Measurable A) (hy : Measurable y) (hx : Measurable x) :
    Measurable (fun z => basePoint base (A z) (y z) (x z)) := by
  have h := (measurable_basePoint (d := d) (k := k) base).comp ((hA.prodMk hy).prodMk hx)
  exact h

@[fun_prop] lemma measurable_baseDensity_comp {X : Type*} [MeasurableSpace X]
    {d k : ℕ} (base : BaseLaw) {A : X → Rows d k} {y : X → Labels k}
    (hA : Measurable A) (hy : Measurable y) :
    Measurable (fun z => baseDensity base (A z) (y z)) := by
  have h := (measurable_baseDensity (d := d) (k := k) base).comp (hA.prodMk hy)
  exact h

@[fun_prop] lemma measurable_kernelComponent_comp {X : Type*} [MeasurableSpace X]
    {d k : ℕ} {A : X → Rows d k} {x : X → Vec d}
    (hA : Measurable A) (hx : Measurable x) :
    Measurable (fun z => kernelComponent (A z) (x z)) := by
  have h := (measurable_kernelComponent (d := d) (k := k)).comp (hA.prodMk hx)
  exact h

@[fun_prop] lemma measurable_labels_comp {X : Type*} [MeasurableSpace X]
    {d k : ℕ} {A : X → Rows d k} {x : X → Vec d}
    (hA : Measurable A) (hx : Measurable x) :
    Measurable (fun z => labels (A z) (x z)) := by
  have h := (measurable_labels (d := d) (k := k)).comp (hA.prodMk hx)
  exact h
end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Gaussian_RandomComplement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[fun_prop] lemma measurable_gramSchmidtNormed {n : ℕ} (i : Fin n) :
    Measurable (fun v : Fin n → E => gramSchmidtNormed ℝ v i) := by
  unfold gramSchmidtNormed
  exact ((PosteriorRegression.measurable_gramSchmidt i).norm.inv).smul
    (PosteriorRegression.measurable_gramSchmidt i)

def randomComplement {ℓ m k : ℕ} (V : Rows ℓ m) (e : Rows ℓ k) : Rows ℓ k :=
  gramSchmidtNormed ℝ (fun i => kernelComponent V (e i))

@[fun_prop] lemma measurable_randomComplement {ℓ m k : ℕ} :
    Measurable (fun z : Rows ℓ m × Rows ℓ k => randomComplement z.1 z.2) := by
  unfold randomComplement
  apply Measurable.of_eval
  intro i
  exact (measurable_gramSchmidtNormed i).comp (by fun_prop)

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Gaussian_GaussianRowMix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

def vecTranspose {d k : ℕ} (A : Rows d k) : Rows k d :=
  fun j => WithLp.toLp 2 (fun i => A i j)

@[fun_prop] lemma measurable_vecTranspose {d k : ℕ} : Measurable (@vecTranspose d k) := by
  unfold vecTranspose
  fun_prop

@[simp] lemma vecTranspose_involutive {d k : ℕ} (A : Rows d k) :
    vecTranspose (vecTranspose A) = A := rfl

def rowMix {d ℓ k : ℕ} (C : Rows ℓ k) (A : Rows d ℓ) : Rows d k :=
  fun i => ∑ j, (C i j) • A j

@[fun_prop] lemma measurable_rowMix {d ℓ k : ℕ} :
    Measurable (fun z : Rows ℓ k × Rows d ℓ => rowMix z.1 z.2) := by
  unfold rowMix
  fun_prop

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Gaussian_GramTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def columnMix {m : ℕ} (v : Fin m → E) (M : Matrix (Fin m) (Fin m) ℝ) : Fin m → E :=
  fun j => ∑ i, M i j • v i

@[fun_prop] lemma measurable_columnMix {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) :
    Measurable (fun v : Fin m → E => columnMix v M) := by
  unfold columnMix
  fun_prop

def pairingColumns {d ℓ m : ℕ} (v : Rows d m) (B : Rows d ℓ) : Rows ℓ m :=
  fun i => WithLp.toLp 2 (fun j => ⟪v i, B j⟫)

@[fun_prop] lemma measurable_pairingColumns {d ℓ m : ℕ} :
    Measurable (fun z : Rows d m × Rows d ℓ => pairingColumns z.1 z.2) := by
  unfold pairingColumns
  fun_prop

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Gaussian_GaussianWishart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

def wishartMoment (ℓ m k : ℕ) : ℝ≥0∞ :=
  ∫⁻ G : Rows ℓ m, ENNReal.ofReal ((gramVolume G)⁻¹^k) ∂gaussianRows ℓ m

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_BaseContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

@[fun_prop] lemma continuous_basePoint_label {d k : ℕ} (base : BaseLaw)
    (A : Rows d k) (x : Vec d) : Continuous (fun y => basePoint base A y x) := by
  cases base <;> unfold basePoint <;> fun_prop

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_TupleMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

@[fun_prop] lemma continuous_differences {d m : ℕ} : Continuous (@differences d m) := by
  unfold differences
  fun_prop

@[fun_prop] lemma continuous_affineVolume {d m : ℕ} : Continuous (@affineVolume d m) := by
  unfold affineVolume
  apply Real.continuous_sqrt.comp
  apply Continuous.matrix_det
  unfold Matrix.gram
  fun_prop

@[simp] lemma differences_cons {d m : ℕ} (p : Vec d) (v : Fin m → Vec d) :
    differences (Fin.cons p v : Tuple d m) = fun j => v j - p := by
  funext j
  simp only [PosteriorReplicas.differences, Fin.cons_succ, Fin.cons_zero]

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Measures_EqualBaseMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

abbrev EqualSpace (d k m : ℕ) := Rows d k × Labels k × Tuple d m
abbrev LeftSource (d k m : ℕ) := Rows d k × Vec d × Rows d m

def leftBaseSource (d k m : ℕ) (base : BaseLaw) : Measure (LeftSource d k m) :=
  (gaussianRows d k).prod ((base.measure d).prod (gaussianRows d m))

instance instIsProbabilityMeasureLeftSourceLeftBaseSourceOfNeZeroNat {d k m : ℕ} [NeZero d] (base : BaseLaw) :
    IsProbabilityMeasure (leftBaseSource d k m base) := by
  unfold leftBaseSource
  infer_instance

def leftBasePoint {d k m : ℕ} (base : BaseLaw) (z : LeftSource d k m) : EqualSpace d k m :=
  (z.1, labels z.1 z.2.1,
    Fin.cons z.2.1 (fun i => basePoint base z.1 (labels z.1 z.2.1) (z.2.2 i)))

def leftBaseWeight {d k m : ℕ} (base : BaseLaw) (z : LeftSource d k m) : ℝ≥0∞ :=
  baseDensity base z.1 (labels z.1 z.2.1) ^ m

@[fun_prop] lemma measurable_leftBasePoint {d k m : ℕ} (base : BaseLaw) :
    Measurable (@leftBasePoint d k m base) := by
  unfold leftBasePoint
  fun_prop

@[fun_prop] lemma measurable_leftBaseWeight {d k m : ℕ} (base : BaseLaw) :
    Measurable (@leftBaseWeight d k m base) := by
  unfold leftBaseWeight
  fun_prop

def leftBaseMeasure (d k m : ℕ) (base : BaseLaw) : Measure (EqualSpace d k m) :=
  ((leftBaseSource d k m base).withDensity (leftBaseWeight base)).map (leftBasePoint base)

@[simp] lemma tiltMass_one {d k : ℕ} (base : BaseLaw) (A : Rows d k) (y : Labels k) :
    tiltMass base (fun _ => 1) A y = 1 := by simp [tiltMass]

@[simp] lemma tiltedFiber_one {d k : ℕ} (base : BaseLaw) (A : Rows d k) (y : Labels k) :
    tiltedFiber base (fun _ => 1) A y = baseFiber base A y := by
  simp [tiltedFiber]

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Measures_EqualApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

def equalApprox {d k m : ℕ} (base : BaseLaw) (n : ℕ)
    (H : EqualSpace d k m → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ A, ∫⁻ u : Tuple d m,
    matrixNoiseDensity m k n (fun i => labels A (u i.succ) - labels A (u 0)) *
      H (A, labels A (u 0), u) ∂Measure.pi (fun _ => base.measure d) ∂gaussianRows d k

def smoothedTail {d k m : ℕ} (base : BaseLaw) (n : ℕ)
    (H : EqualSpace d k m → ℝ≥0∞) (A : Rows d k) (p : Vec d) : ℝ≥0∞ :=
  ∫⁻ v : Fin m → Vec d, matrixNoiseDensity m k n (fun i => labels A (v i) - labels A p) *
    H (A, labels A p, Fin.cons p v) ∂Measure.pi (fun _ => base.measure d)

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Measures_EqualRightMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

abbrev RightSource (d k m : ℕ) := Tuple d m × Rows d k

def rightBaseSource (d k m : ℕ) (base : BaseLaw) : Measure (RightSource d k m) :=
  (Measure.pi (fun _ : Fin (m+1) => base.measure d)).prod (gaussianRows d k)

instance instIsProbabilityMeasureRightSourceRightBaseSourceOfNeZeroNat {d k m : ℕ} [NeZero d] (base : BaseLaw) :
    IsProbabilityMeasure (rightBaseSource d k m base) := by
  unfold rightBaseSource
  infer_instance

def equalConstant (k m : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((2 * Real.pi) ^ (-(k * m : ℝ) / 2))

def rightBaseWeight {d k m : ℕ} (z : RightSource d k m) : ℝ≥0∞ :=
  equalConstant k m * (ENNReal.ofReal (affineVolume z.1))⁻¹ ^ k

def residualRows {d k m : ℕ} (u : Tuple d m) (A : Rows d k) : Rows d k :=
  fun j => kernelComponent (differences u) (A j)

def rightBasePoint {d k m : ℕ} (z : RightSource d k m) : EqualSpace d k m :=
  (residualRows z.1 z.2, labels (residualRows z.1 z.2) (z.1 0), z.1)

@[fun_prop] lemma measurable_residualRows {d k m : ℕ} :
    Measurable (fun z : RightSource d k m => residualRows z.1 z.2) := by
  unfold residualRows
  fun_prop

@[fun_prop] lemma measurable_rightBasePoint {d k m : ℕ} :
    Measurable (@rightBasePoint d k m) := by unfold rightBasePoint; fun_prop

@[fun_prop] lemma measurable_rightBaseWeight {d k m : ℕ} :
    Measurable (@rightBaseWeight d k m) := by unfold rightBaseWeight; fun_prop

def rightBaseMeasure (d k m : ℕ) (base : BaseLaw) : Measure (EqualSpace d k m) :=
  ((rightBaseSource d k m base).withDensity rightBaseWeight).map rightBasePoint

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Measures_DensityDifferentiation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal NNReal Topology
noncomputable section
namespace PosteriorReplicas

@[fun_prop] lemma continuous_labelNorm {k : ℕ} : Continuous (@labelNorm k) := by
  unfold labelNorm
  fun_prop

@[fun_prop] lemma measurable_ballDensityVersion {d k : ℕ} (ν : Measure (Vec d)) [SFinite ν] :
    Measurable (fun z : Rows d k × Labels k => ballDensityVersion ν z.1 z.2) := by
  unfold ballDensityVersion
  apply Measurable.liminf
  intro n
  apply Measurable.const_mul
  exact measurable_measure_prodMk_left (show MeasurableSet
    {z : (Rows d k × Labels k) × Vec d |
      labelNorm (labels z.1.1 z.2 - z.1.2) < (n + 1 : ℝ)⁻¹} from
    measurableSet_lt (continuous_labelNorm.measurable.comp (by fun_prop)) measurable_const)

@[fun_prop] lemma measurable_gaussianDensityVersion {d k : ℕ} (ν : Measure (Vec d)) [SFinite ν] :
    Measurable (fun z : Rows d k × Labels k => gaussianDensityVersion ν z.1 z.2) := by
  unfold gaussianDensityVersion
  apply Measurable.liminf
  intro n
  apply Measurable.lintegral_prod_right
  apply ENNReal.measurable_ofReal.comp
  fun_prop

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Measures_EuclideanLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal NNReal Topology
noncomputable section
namespace PosteriorReplicas

def euclideanLabelLaw {d k : ℕ} (ν : Measure (Vec d)) (A : Rows d k) : Measure (Vec k) :=
  ν.map (fun x => WithLp.toLp 2 (labels A x))

instance instIsFiniteMeasureVecEuclideanLabelLaw {d k : ℕ} (ν : Measure (Vec d)) [IsFiniteMeasure ν] (A : Rows d k) :
    IsFiniteMeasure (euclideanLabelLaw ν A) := by unfold euclideanLabelLaw; infer_instance

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Measures_GaussianDifferentiation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal NNReal Topology
noncomputable section
namespace PosteriorReplicas

section Generic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

def radialLevel (E : Type*) [NormedAddCommGroup E] (t : ℝ) : Set E :=
  {x | t < Real.exp (-‖x‖^2 / 2)}

def radialWeight (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2)) * volume (radialLevel E t)

omit [Nontrivial E] in
@[fun_prop] lemma measurable_radialWeight [Nontrivial E] : Measurable (radialWeight E) := by
  unfold radialWeight radialLevel
  apply Measurable.const_mul
  exact measurable_measure_prodMk_left (show MeasurableSet
    {z : ℝ × E | z.1 < Real.exp (-‖z.2‖^2/2)} from measurableSet_lt (by fun_prop) (by fun_prop))

def scaledRadial (n : ℕ) (y x : E) : ℝ≥0∞ :=
  (ENNReal.ofReal ((noiseScale n) ^ Module.finrank ℝ E))⁻¹ *
    gaussianRadialDensity (Module.finrank ℝ E) (‖x-y‖ / noiseScale n)

end Generic
end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_DensityBinsGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

def tupleDistance {d m : ℕ} (u : Tuple d m) (x : Vec d) : ℝ :=
  ‖(differenceSpan u)ᗮ.starProjection (x-u 0)‖

@[fun_prop] lemma measurable_tupleDistance_fixed {d m : ℕ} (u : Tuple d m) :
    Measurable (tupleDistance u) := by unfold tupleDistance; fun_prop

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_LabelConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

def ellipsoidMass {d k : ℕ} (ν : Measure (Vec d)) (A : Rows d k) (y : Labels k) (r : ℝ) : ℝ≥0∞ :=
  ν {x | ‖liftLabel A (labels A x-y)‖ ≤ r}

@[fun_prop] lemma measurable_ellipsoidMass {d k : ℕ} (ν : Measure (Vec d)) [SFinite ν] (r : ℝ) :
    Measurable (fun z : Data d k => ellipsoidMass ν z.1 z.2 r) := by
  change Measurable (fun z : Data d k => ν ((Prod.mk z) ⁻¹'
    {q : Data d k × Vec d | ‖liftLabel q.1.1 (labels q.1.1 q.2-q.1.2)‖ ≤ r}))
  apply measurable_measure_prodMk_left
  exact measurableSet_le (by unfold labels; fun_prop) measurable_const

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Kernels_ReplicaMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace PosteriorReplicas

def equalReference {d k m : ℕ} (ν : Measure (Vec d)) : Measure (EqualSpace d k m) :=
  ((Measure.pi (fun _ : Fin (m+1) => ν)).prod (gaussianRows d k)).map rightBasePoint

instance instIsProbabilityMeasureEqualSpaceEqualReferenceOfVec {d k m : ℕ} (ν : Measure (Vec d)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (equalReference (k := k) (m := m) ν) := by
  unfold equalReference
  exact Measure.isProbabilityMeasure_map (by fun_prop)

instance instIsFiniteMeasureEqualSpaceEqualReferenceOfVec {d k m : ℕ} (ν : Measure (Vec d)) [IsFiniteMeasure ν] :
    IsFiniteMeasure (equalReference (k := k) (m := m) ν) := by
  unfold equalReference
  infer_instance

def replicaDensity {d k m : ℕ} (base : BaseLaw) (f : Vec d → ℝ≥0∞)
    (z : EqualSpace d k m) : ℝ≥0∞ :=
  equalConstant k m * (ENNReal.ofReal (affineVolume z.2.2))⁻¹ ^ k *
    (projectedDensity base f z.1 z.2.1)⁻¹ ^ m

@[fun_prop] lemma measurable_replicaDensity {d k m : ℕ} (base : BaseLaw)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) : Measurable (@replicaDensity d k m base f) := by
  unfold replicaDensity
  fun_prop

def replicaLaw {d k m : ℕ} (base : BaseLaw) (f : Vec d → ℝ≥0∞) : Measure (EqualSpace d k m) :=
  (equalReference ((base.measure d).withDensity f)).withDensity (replicaDensity base f)

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_DensityBinEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

def expectedDensity {d k m : ℕ} (f : Vec d → ℝ≥0∞) (u : Tuple d m) : ℝ≥0∞ :=
  ∫⁻ A, projectedDensity .spherical f (residualRows u A)
    (labels (residualRows u A) (u 0)) ∂gaussianRows d k

@[fun_prop] lemma measurable_expectedDensity {d k m : ℕ} {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) : Measurable (@expectedDensity d k m f) := by
  unfold expectedDensity
  fun_prop

def binEnvelope {d k : ℕ} (ν : Measure (Vec d)) (J : ℕ) (A : Rows d k) (y : Labels k) : ℝ≥0∞ :=
  2 + ∑ j ∈ Finset.range J, ENNReal.ofReal ((2:ℝ)^(k*(j+1))) * ellipsoidMass ν A y ((1/2:ℝ)^j)

@[fun_prop] lemma measurable_binEnvelope {d k : ℕ} (ν : Measure (Vec d)) [SFinite ν] (J : ℕ) :
    Measurable (fun z : Data d k => binEnvelope ν J z.1 z.2) := by
  unfold binEnvelope
  fun_prop

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_BinCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

def binCutoff (d k : ℕ) (L : ℝ) : ℕ := 7*d+k+2+Nat.ceil (2*Real.log L)

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Kernels_KernelPi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

@[fun_prop] lemma measurable_fin_cons {Y : Type*} [MeasurableSpace Y] {n : ℕ} :
    Measurable (fun z : Y × (Fin n → Y) => (Fin.cons z.1 z.2 : Fin (n+1) → Y)) := by
  apply measurable_pi_iff.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero] using (measurable_fst : Measurable (Prod.fst : Y × (Fin n → Y) → Y))
  · simpa only [Fin.cons_succ, Function.comp_def] using (measurable_pi_apply j).comp measurable_snd

def piKernel {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] :
    {n : ℕ} → (Fin n → Kernel X Y) → Kernel X (Fin n → Y)
  | 0, _ => Kernel.deterministic (fun _ i => Fin.elim0 i) (by fun_prop)
  | n+1, κ => ((κ 0) ×ₖ piKernel (fun i : Fin n => κ i.succ)).map
      (fun z => Fin.cons z.1 z.2)

instance piKernel_markov {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {n : ℕ} (κ : Fin n → Kernel X Y) [∀ i, IsMarkovKernel (κ i)] :
    IsMarkovKernel (piKernel κ) := by
  induction n with
  | zero => unfold piKernel; infer_instance
  | succ n ih =>
    have : IsMarkovKernel (piKernel (fun i : Fin n => κ i.succ)) := ih _
    unfold piKernel
    exact Kernel.IsMarkovKernel.map _ (by fun_prop)

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_PiKL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

def coordinateMarginal {Y : Type*} [MeasurableSpace Y] {n : ℕ}
    (q : Measure (Fin n → Y)) (i : Fin n) : Measure Y := q.map (fun u => u i)

instance coordinateMarginal_probability {Y : Type*} [MeasurableSpace Y] {n : ℕ}
    (q : Measure (Fin n → Y)) [IsProbabilityMeasure q] (i : Fin n) :
    IsProbabilityMeasure (coordinateMarginal q i) :=
  (Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable : IsProbabilityMeasure (q.map (fun u => u i)))

def marginalProduct {Y : Type*} [MeasurableSpace Y] {n : ℕ}
    (q : Measure (Fin n → Y)) : Measure (Fin n → Y) := Measure.pi (coordinateMarginal q)

instance marginalProduct_probability {Y : Type*} [MeasurableSpace Y] {n : ℕ}
    (q : Measure (Fin n → Y)) [IsProbabilityMeasure q] : IsProbabilityMeasure (marginalProduct q) := by
  unfold marginalProduct
  infer_instance

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_ConditionalPiKL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

section ConditionalPi
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace Y] [Nonempty Y] {n : ℕ}
  (μ : Measure X) [IsProbabilityMeasure μ]
  (κ : Kernel X (Fin n → Y)) [IsMarkovKernel κ]

def coordKernel (i : Fin n) : Kernel X Y := κ.map (fun u => u i)
instance coordKernel_markov (i : Fin n) : IsMarkovKernel (coordKernel κ i) :=
  Kernel.IsMarkovKernel.map _ (measurable_pi_apply i)

def conditionalTotalCorrelation : ℝ≥0∞ :=
  klDiv (μ ⊗ₘ κ) (μ ⊗ₘ piKernel (coordKernel κ))

end ConditionalPi

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_GraphKL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

def attachSide {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (g : X → Z) (q : Measure (X × Y)) : Measure (Z × (X × Y)) :=
  q.map (fun z => (g z.1, z))

instance attachSide_finite {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (g : X → Z) (q : Measure (X × Y)) [IsFiniteMeasure q] :
    IsFiniteMeasure (attachSide g q) := by
  unfold attachSide
  infer_instance

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_ReplicaInformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

def mutualInformation {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (q : Measure (X × Y)) : ℝ≥0∞ := klDiv q (q.fst.prod q.snd)

def totalCorrelation {Y : Type*} [MeasurableSpace Y] {n : ℕ}
    (q : Measure (Fin n → Y)) : ℝ≥0∞ := klDiv q (marginalProduct q)

section Coordinates
variable {W Y : Type*} [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]
  [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y] {n : ℕ}
  (μ : Measure W) [IsProbabilityMeasure μ] (κ : Kernel W (Fin n → Y)) [IsMarkovKernel κ]

def coordinateJoint (i : Fin n) : Measure (Y × W) :=
  (μ ⊗ₘ coordKernel κ i).map Prod.swap

instance coordinateJoint_probability (i : Fin n) : IsProbabilityMeasure (coordinateJoint μ κ i) := by
  unfold coordinateJoint
  exact Measure.isProbabilityMeasure_map (by fun_prop)

end Coordinates

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_ParametricKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

section
variable {T U V : Type*} [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]

def parametricMapKernel (q : Measure U) (h : T × U → V) : Kernel T V :=
  (Kernel.id ×ₖ Kernel.const T q).map h

instance parametricMapKernel_sfinite (q : Measure U) [SFinite q]
    (h : T × U → V) : IsSFiniteKernel (parametricMapKernel q h) := by
  unfold parametricMapKernel
  infer_instance

end

section RandomSide
variable {T X Y Z : Type*} [MeasurableSpace T] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Y] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Y]

def randomSideLaw (μ : Measure T) (g : T × X → Z) (q : Measure (X × Y)) :
    Measure ((T × Z) × (X × Y)) :=
  (μ.prod q).map (fun z => ((z.1,g (z.1,z.2.1)),z.2))

instance randomSideLaw_finite (μ : Measure T) [IsFiniteMeasure μ]
    (g : T × X → Z) (q : Measure (X × Y)) [IsFiniteMeasure q] :
    IsFiniteMeasure (randomSideLaw μ g q) := by unfold randomSideLaw; infer_instance

end RandomSide

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_HaarInformationEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace PosteriorReplicas

@[fun_prop] lemma measurable_gramSchmidtNormed_rows {d ℓ : ℕ} :
    Measurable (gramSchmidtNormed ℝ : Rows d ℓ → Rows d ℓ) :=
  Measurable.of_eval (fun index => measurable_gramSchmidtNormed index)

instance haarRows_probability (d ℓ : ℕ) : IsProbabilityMeasure (haarRows d ℓ) := by
  unfold haarRows
  exact Measure.isProbabilityMeasure_map (by fun_prop)

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_ObservableLikelihood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

abbrev AuxSpace (d ℓ k : ℕ) := Rows d ℓ × Rows ℓ k

def auxLaw (d ℓ k : ℕ) : Measure (AuxSpace d ℓ k) :=
  (gaussianRows d ℓ).prod (gaussianRows ℓ k)

instance instIsProbabilityMeasureAuxSpaceAuxLaw (d ℓ k : ℕ) : IsProbabilityMeasure (auxLaw d ℓ k) := by
  unfold auxLaw; infer_instance

def projectedTuple {d ℓ m : ℕ} (B : Rows d ℓ) (u : Tuple d m) : Tuple ℓ m :=
  fun i => WithLp.toLp 2 (labels B (u i))

@[fun_prop] lemma measurable_projectedTuple {d ℓ m : ℕ} :
    Measurable (fun z : Rows d ℓ × Tuple d m => projectedTuple z.1 z.2) := by
  unfold projectedTuple labels; fun_prop

def observableRows {d ℓ k m : ℕ} (u : Tuple d m) (b : AuxSpace d ℓ k) : Rows d k :=
  rowMix (randomComplement (pairingColumns (differences u) b.1) b.2) b.1

@[fun_prop] lemma measurable_observableRows {d ℓ k m : ℕ} :
    Measurable (fun z : Tuple d m × AuxSpace d ℓ k => observableRows z.1 z.2) := by
  unfold observableRows; fun_prop

abbrev Observation (d ℓ k m : ℕ) := AuxSpace d ℓ k × Tuple ℓ m

def observe {d ℓ k m : ℕ} (z : EqualSpace d k m × AuxSpace d ℓ k) : Observation d ℓ k m :=
  (z.2,projectedTuple z.2.1 z.1.2.2)

@[fun_prop] lemma measurable_observe {d ℓ k m : ℕ} : Measurable (@observe d ℓ k m) := by
  unfold observe; fun_prop

def observableLikelihood {d ℓ k m : ℕ} (f : Vec d → ℝ≥0∞)
    (z : Observation d ℓ k m) : ℝ≥0∞ :=
  let C := randomComplement (differences z.2) z.1.2
  equalConstant k m * (wishartMoment ℓ m k)⁻¹ *
    (ENNReal.ofReal (affineVolume z.2))⁻¹^k *
      (projectedDensity .spherical f (rowMix C z.1.1)
        (fun i => ⟪C i,z.2 0⟫))⁻¹^m

@[fun_prop] lemma measurable_observableLikelihood {d ℓ k m : ℕ} {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) : Measurable (@observableLikelihood d ℓ k m f) := by
  unfold observableLikelihood; fun_prop

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_NormalizedLikelihood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

def observableLog {d ℓ k m : ℕ} (f : Vec d → ℝ≥0∞) (z : Observation d ℓ k m) : ℝ :=
  Real.log (observableLikelihood f z).toReal

@[fun_prop] lemma measurable_observableLog {d ℓ k m : ℕ} {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) : Measurable (@observableLog d ℓ k m f) := by unfold observableLog; fun_prop

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Kernels_PosteriorKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

@[fun_prop] lemma measurable_tiltedFiber {d k : ℕ} (base : BaseLaw)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun z : Data d k => tiltedFiber base f z.1 z.2) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have ht := measurable_tiltMass (d := d) (k := k) base hf
  have hm : Measurable (fun z : Data d k => (baseFiber base z.1 z.2).withDensity f s) := by
    simp only [withDensity_apply _ hs]
    simpa only [lintegral_indicator hs, baseKernel, Kernel.coe_mk] using
      (hf.indicator hs).lintegral_kernel (κ := baseKernel base)
  have he : (fun z : Data d k => tiltedFiber base f z.1 z.2 s) =
      fun z => if tiltMass base f z.1 z.2 = 0 then (Measure.dirac (0 : Vec d)) s
        else (tiltMass base f z.1 z.2)⁻¹ * (baseFiber base z.1 z.2).withDensity f s := by
    funext z
    unfold tiltedFiber
    split_ifs <;> simp [Measure.smul_apply]
  rw [he]
  exact Measurable.ite (measurableSet_eq_fun ht measurable_const) measurable_const (ht.inv.mul hm)

def posteriorKernel {d k : ℕ} (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f) :
    Kernel (Data d k) (Vec d) where
  toFun z := tiltedFiber base f z.1 z.2
  measurable' := measurable_tiltedFiber base hf

def dataLaw {d k : ℕ} (ν : Measure (Vec d)) : Measure (Data d k) :=
  ((gaussianRows d k).prod ν).map (fun z => (z.1,labels z.1 z.2))

instance instIsProbabilityMeasureDataDataLawOfVec {d k : ℕ} (ν : Measure (Vec d)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (dataLaw (k := k) ν) := by
  unfold dataLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Kernels_DensityRatio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

def normalizedRatio {d ℓ k m : ℕ} (f : Vec d → ℝ≥0∞)
    (z : EqualSpace d k m × AuxSpace d ℓ k) : ℝ≥0∞ :=
  (projectedDensity .spherical f (observableRows z.1.2.2 z.2)
    (labels (observableRows z.1.2.2 z.2) (z.1.2.2 0))) *
      (projectedDensity .spherical f z.1.1 z.1.2.1)⁻¹ * (ENNReal.ofReal (gramVolume z.1.1))⁻¹

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Kernels_ReplicaGaussianMarginals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

def projectionGramRatio {d ℓ k m : ℕ} (z : EqualSpace d k m × AuxSpace d ℓ k) : ℝ :=
  gramVolume (pairingColumns (differences z.1.2.2) z.2.1) / affineVolume z.1.2.2

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_ReplicaLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Matrix InnerProductSpace Filter Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

def binMeanBound (k J : ℕ) : ℝ :=
  (volume {y : Labels k | labelNorm y ≤ 1}).toReal * (2+(J:ℝ)*2^k)

def comparisonEnvelope {d ℓ k m : ℕ} (f : Vec d → ℝ≥0∞) (J : ℕ)
    (z : EqualSpace d k m × AuxSpace d ℓ k) : ℝ :=
  Real.log (wishartMoment ℓ m k).toReal + (k:ℝ)*Real.log (projectionGramRatio z) +
    (m:ℝ)*Real.log (gramVolume z.1.1) +
      (m:ℝ)*(Real.log (binMeanBound k J) + (normalizedRatio f z).toReal / binMeanBound k J - 1)

def comparisonCost (d ℓ k m J : ℕ) : ℝ :=
  Real.log (wishartMoment ℓ m k).toReal + (k:ℝ)*((m:ℝ)/2*Real.log ((ℓ:ℝ)+1)) +
    (m:ℝ)*((k:ℝ)/2*Real.log ((d:ℝ)+1)) + (m:ℝ)*Real.log (binMeanBound k J)

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_StateExperiment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

def initialStateKernel {d V : ℕ} (q : Measure (Vec d × Fin V)) [IsFiniteMeasure q] :
    Kernel (Fin V) (Vec d) := (q.map Prod.swap).condKernel

instance instIsMarkovKernelFinVecInitialStateKernel {d V : ℕ} (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q] :
    IsMarkovKernel (initialStateKernel q) := by unfold initialStateKernel; infer_instance

def stateBlockKernel {d k V W : ℕ} (κ : Kernel (Fin V × Data d k) (Fin W)) (v : Fin V) :
    Kernel (Data d k) (Fin W) := κ.comap (fun z => (v,z)) (by fun_prop)

instance instIsMarkovKernelDataFinStateBlockKernelOfProd {d k V W : ℕ} (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ] (v : Fin V) :
    IsMarkovKernel (stateBlockKernel κ v) := by unfold stateBlockKernel; infer_instance

def stateOutputKernel {d k V W : ℕ} (q : Measure (Vec d × Fin V)) [IsFiniteMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) : Kernel (Fin V) (Vec d × Fin W) :=
  Kernel.ofFunOfCountable (fun v => signalMessageLaw (initialStateKernel q v) (stateBlockKernel κ v))

instance instIsMarkovKernelFinProdVecStateOutputKernelOfData {d k V W : ℕ} (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ] :
    IsMarkovKernel (stateOutputKernel q κ) where
  isProbabilityMeasure v := inferInstanceAs
    (IsProbabilityMeasure (signalMessageLaw (initialStateKernel q v) (stateBlockKernel κ v)))

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_StateSide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

def stateSideKernel {d k V W : ℕ} (ℓ : ℕ)
    (q : Measure (Vec d × Fin V)) [IsFiniteMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) :
    Kernel (Fin V) (Data d ℓ × (Vec d × Fin W)) :=
  Kernel.ofFunOfCountable (fun v => randomSideLaw (haarRows d ℓ)
    (fun z => labels z.1 z.2) (stateOutputKernel q κ v))

instance instIsMarkovKernelFinProdDataVecStateSideKernel {d k V W : ℕ} (ℓ : ℕ)
    (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ] :
    IsMarkovKernel (stateSideKernel ℓ q κ) where
  isProbabilityMeasure v := by
    change IsProbabilityMeasure ((haarRows d ℓ).prod (stateOutputKernel q κ v) |>.map
      (fun z => ((z.1,labels z.1 z.2.1),z.2)))
    exact Measure.isProbabilityMeasure_map (by fun_prop)

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Kernels_PosteriorExperiment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

def posteriorMessageLaw {d k m N : ℕ} (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    (κ : Kernel (Data d k) (Fin N)) : Measure (Tuple d m × Fin N) :=
  (dataLaw (k := k) ((base.measure d).withDensity f) ⊗ₘ
    (piKernel (fun _ : Fin (m+1) => posteriorKernel base hf) ×ₖ κ)).snd

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Learners_LearnerModelBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
namespace Learner

structure UniformAdmissible {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) : Prop where
  transition : ∀ᵐ ω ∂ρ, ∀ t a,
    AEMeasurable (fun obs => (L.transition t ω a obs).2) (observationReference d)
  uniform_experiment : AEMeasurable
    (fun z : UnitSphere d × (Ω × Samples d T) => L.estimate z.1 z.2.1 z.2.2)
    ((uniformSphere d).prod (ρ.prod (sampleLaw d T)))

end Learner

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Learners_KernelLearnerBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal NNReal RealInnerProductSpace unitInterval
noncomputable section
namespace PosteriorRegression

namespace Learner

instance runStatus_measurableSingleton (M : ℕ) : MeasurableSingletonClass (RunStatus M) where
  measurableSet_singleton r := by
    rcases r with a | done
    · simpa only [Set.image_singleton] using (measurableSet_inl_image (β := ℕ × State M) (s := {a})).mpr (measurableSet_singleton a)
    · simpa only [Set.image_singleton] using (measurableSet_inr_image (α := State M) (s := {done})).mpr (measurableSet_singleton done)

end Learner
end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Learners_CompletedKernelLearner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal NNReal RealInnerProductSpace unitInterval
noncomputable section
namespace PosteriorRegression

namespace CompletedKernelLearner

structure Realization {d M : ℕ} (K : CompletedKernelLearner d M) where
  initial : unitInterval → Destination M
  measurable_initial : Measurable initial
  law_initial : volume.map initial = K.initial
  transition : ℕ → State M → (Vector d × ℝ) → unitInterval → Destination M
  measurable_transition : ∀ t a, @Measurable (CompletedObservation d × unitInterval)
    (Destination M) _ _ (uncurry (transition t a))
  law_transition : ∀ t a obs, volume.map (transition t a obs) = K.transition t a obs
  output : ℕ → State M → unitInterval → UnitSphere d
  measurable_output : ∀ t a, Measurable (output t a)
  law_output : ∀ t a, volume.map (output t a) = K.output t a

lemma exists_realization {d M : ℕ} (K : CompletedKernelLearner d M) : Nonempty (Realization K) := by
  have : Nonempty (UnitSphere d) := nonempty_of_isProbabilityMeasure (K.output 0 0)
  obtain ⟨i,hi,hiLaw⟩ := K.initial.exists_measurable_map_eq
  choose δ hδ hδLaw using (fun t a => (K.transition t a).exists_measurable_map_eq_unitInterval)
  choose o ho hoLaw using (fun t a => (K.output t a).exists_measurable_map_eq)
  exact ⟨⟨i,hi,hiLaw,δ,hδ,hδLaw,o,ho,hoLaw⟩⟩

def realization {d M : ℕ} (K : CompletedKernelLearner d M) : Realization K :=
  Classical.choice K.exists_realization

abbrev Coins (T : ℕ) := Fin (T+2) → unitInterval

def coinsLaw (T : ℕ) : Measure (Coins T) := Measure.pi (fun _ => volume)

instance coinsLaw_probability (T : ℕ) : IsProbabilityMeasure (coinsLaw T) := by
  unfold coinsLaw
  infer_instance

def Realization.toLearner {d M : ℕ} {K : CompletedKernelLearner d M}
    (R : Realization K) (T : ℕ) : Learner d M T (Coins T) where
  initialChoice ω := R.initial (ω 0)
  transition t ω a obs := if ht : t≤T then R.transition t a obs (ω ⟨t,by omega⟩) else (false,a)
  output t ω a := R.output t a (ω ⟨T+1,by omega⟩)

end CompletedKernelLearner
end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Learners_CompletedKernelLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal NNReal RealInnerProductSpace unitInterval
noncomputable section
namespace PosteriorRegression

namespace CompletedKernelLearner
open Learner

def Realization.stepMap {d M T : ℕ} {K : CompletedKernelLearner d M} (R : Realization K)
    (s : UnitSphere d) (x : Samples d T) (i : Fin T) : RunStatus M × unitInterval → RunStatus M
  | (.inr done,_) => .inr done
  | (.inl a,u) => destStatus (i.val+1) (R.transition (i.val+1) a (x i,⟪x i,s.val⟫) u)

def fillCoins {T : ℕ} (A : Finset (Fin (T+2))) (u : A → unitInterval) : Coins T :=
  fun j => if hj : j∈A then u ⟨j,hj⟩ else 0

end CompletedKernelLearner
end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Learners_KernelSuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal NNReal RealInnerProductSpace unitInterval
noncomputable section
namespace PosteriorRegression

namespace CompletedKernelLearner
open Learner

def uniformSuccess {d M : ℕ} (K : CompletedKernelLearner d M) (T : ℕ) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : UnitSphere d × Samples d T,
    K.estimateLaw z.1 z.2 {ŝ | angularError z.1 ŝ ≤ ε}
    ∂((uniformSphere d).prod (sampleLaw d T))

end CompletedKernelLearner
end PosteriorRegression
end

end OAI
end


