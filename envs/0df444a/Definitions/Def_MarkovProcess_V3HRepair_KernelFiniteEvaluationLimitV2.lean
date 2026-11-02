-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_KernelFiniteEvaluationLimitV2
-- name    : MarkovProcess_V3HRepair_KernelFiniteEvaluationLimitV2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T10:09:58.534253+00:00
-- url     : https://prove2.me/theorems/da1a96b3-9261-4c00-afe5-cf144b6d9f40
-- title:
--   Verified MarkovProcess source repair: KernelFiniteEvaluationLimit V2
-- statement:
--   Finite evaluation of continuous paths is measurable, and convergence of finite-time evaluations and integrals identifies corresponding kernel pushforwards. Finite-time evaluation convergence is proved directly from continuity of each path.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream commit 1f8060caa137731fa08029592019eeaf9d997fe5; source-faithful adapted proof module V3HRepaired.KernelFiniteEvaluationLimit, archived SHA-256 336cb79b8a57e11a9e936f4dcf7bbbbe8a4bedc4bc009d5d2bf88cbe2d9d20a7. V2 replaces one missing helper call with direct coordinatewise convergence, using tendsto_pi_nhds and path continuity.

import Definitions.Def_MarkovProcess_V3H_Feller_Semigroup_2cfe612a
import Definitions.Def_MarkovProcess_V3H_Kernel_C0SemigroupJoint_9aea0383
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMeasure_354455bb
import Definitions.Def_MarkovProcess_V3H_Trajectory_AllTimeFiniteMarginals_51403fc5
import Definitions.Def_MarkovProcess_V3H_Trajectory_Basic_34bd0835
import Definitions.Def_MarkovProcess_V3H_Trajectory_FiniteMarginals_a8fbfae5
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.IsLUB

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal
namespace MarkovProcess
noncomputable section
variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] [LocallyCompactSpace α]

omit [SecondCountableTopology α] [LocallyCompactSpace α] in
/-- Simultaneous evaluation at finitely many fixed times is Borel measurable. -/
theorem ContinuousPath.measurable_finiteEvaluation {ι : Type*} [Finite ι]
    (τ : ι → NNReal) : Measurable (finiteEvaluation (α := α) τ) := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_coordinateProcess (alpha := α) (τ i)

omit [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α]
  [LocallyCompactSpace α] in
/-- Dominated convergence for a compactly supported test function evaluated at a convergent
finite family of times along a continuous-path probability kernel.  This is the path-side limit
needed in every finite-dimensional rational approximation argument. -/
theorem tendsto_integral_continuousPath_finiteEvaluation
    {β ι : Type*} [MeasurableSpace β] [Fintype ι]
    (K : Kernel β (ContinuousPath α)) (hK : IsMarkovKernel K)
    (x : β) (f : CompactlySupportedContinuousMap (ι → α) ℝ)
    (τ : ι → NNReal)
    (q : ℕ → ι → NNReal)
    (hq : ∀ i, Tendsto (fun k ↦ q k i) atTop (nhds (τ i))) :
    Tendsto
      (fun k ↦ ∫ path, f (ContinuousPath.finiteEvaluation (α := α) (q k) path) ∂K x)
      atTop
      (nhds (∫ path, f (ContinuousPath.finiteEvaluation (α := α) τ path) ∂K x)) := by
  let : IsMarkovKernel K := hK
  let f0 : ZeroAtInftyContinuousMap (ι → α) ℝ :=
    PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f
  apply tendsto_integral_filter_of_norm_le_const
  · filter_upwards [] with k
    exact (f.continuous.comp
      (ContinuousPath.continuous_finiteEvaluation (q k))).aestronglyMeasurable
  · refine ⟨‖f0‖, Filter.Eventually.of_forall fun k ↦ ?_⟩
    filter_upwards [] with path
    simpa only [f0, PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply,
      Real.norm_eq_abs] using! f0.toBCF.norm_coe_le_norm
      (ContinuousPath.finiteEvaluation (α := α) (q k) path)
  · filter_upwards [] with path
    apply f.continuous.continuousAt.tendsto.comp
    rw [tendsto_pi_nhds]
    intro i
    exact path.continuous.continuousAt.tendsto.comp (hq i)

/-- Equality of finite-dimensional laws passes from approximating time families to their limit
once the comparison kernels have the corresponding compactly-supported-test convergence.

The convergence premise is deliberately stated at precisely the analytic seam: it says nothing
about a Markov property and is exactly the weak/vague continuity of the candidate finite-time
laws needed by the proof. -/
theorem Kernel.map_finiteEvaluation_eq_of_integral_tendsto
    {β ι : Type*} [MeasurableSpace β] [Fintype ι]
    (K : Kernel β (ContinuousPath α)) (hK : IsMarkovKernel K)
    (Lseq : ℕ → Kernel β (ι → α)) (L : Kernel β (ι → α))
    (hL : IsMarkovKernel L) (τ : ι → NNReal) (q : ℕ → ι → NNReal)
    (hq : ∀ i, Tendsto (fun k ↦ q k i) atTop (nhds (τ i)))
    (hlaw : ∀ k, K.map (ContinuousPath.finiteEvaluation (q k)) = Lseq k)
    (hfinite : ∀ (x : β) (f : CompactlySupportedContinuousMap (ι → α) ℝ),
      Tendsto (fun k ↦ ∫ y, f y ∂Lseq k x) atTop (nhds (∫ y, f y ∂L x))) :
    K.map (ContinuousPath.finiteEvaluation τ) = L := by
  let : IsMarkovKernel K := hK
  let : IsMarkovKernel L := hL
  apply Kernel.ext
  intro x
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hpath := tendsto_integral_continuousPath_finiteEvaluation
    K hK x f τ q hq
  have heq : ∀ k,
      (∫ path, f (ContinuousPath.finiteEvaluation (q k) path) ∂K x) =
        ∫ y, f y ∂Lseq k x := by
    intro k
    have hm := congrArg (fun κ : Kernel β (ι → α) ↦ κ x) (hlaw k)
    have hi := congrArg (fun μ : Measure (ι → α) ↦ ∫ y, f y ∂μ) hm
    change (∫ y, f y ∂(K.map (ContinuousPath.finiteEvaluation (q k))) x) =
      ∫ y, f y ∂Lseq k x at hi
    have heval : Measurable (ContinuousPath.finiteEvaluation (α := α) (q k)) :=
      ContinuousPath.measurable_finiteEvaluation (q k)
    have hmap :
        (K.map (ContinuousPath.finiteEvaluation (q k))) x =
          (K x).map (ContinuousPath.finiteEvaluation (q k)) :=
      Kernel.map_apply K heval x
    rw [hmap, integral_map] at hi
    · exact hi
    · exact heval.aemeasurable
    · exact f.continuous.aestronglyMeasurable
  have hsame :
      (fun k ↦ ∫ path, f (ContinuousPath.finiteEvaluation (q k) path) ∂K x) =
        fun k ↦ ∫ y, f y ∂Lseq k x :=
    funext heq
  rw [hsame] at hpath
  have hlimit := tendsto_nhds_unique hpath (hfinite x f)
  have heval : Measurable (ContinuousPath.finiteEvaluation (α := α) τ) :=
    ContinuousPath.measurable_finiteEvaluation τ
  have hmap :
      (K.map (ContinuousPath.finiteEvaluation τ)) x =
        (K x).map (ContinuousPath.finiteEvaluation τ) :=
    Kernel.map_apply K heval x
  rw [hmap, integral_map]
  · exact hlimit
  · exact heval.aemeasurable
  · exact f.continuous.aestronglyMeasurable

end
end MarkovProcess


