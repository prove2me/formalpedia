-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_ContinuousFiniteDenseApproximation
-- name    : MarkovProcess_V3HRepair_ContinuousFiniteDenseApproximation
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T10:02:28.510386+00:00
-- url     : https://prove2.me/theorems/d36fc4e9-8e39-42f6-b530-4605923355ef
-- title:
--   Verified MarkovProcess source repair: ContinuousFiniteDenseApproximation
-- statement:
--   Measurable reindexing of finite rational-time approximations and the exact finite-dimensional marginals of the associated continuous-path trajectory.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream commit 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.ContinuousFiniteDenseApproximation SHA-256 f0d70f44362fec5dc61843a60311db0535b7add8aad03d40362bfced9ef89b3d. Only repaired import paths were translated to the published Definitions.Def_MarkovProcess_V3HRepair_* module names.

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
import Definitions.Def_MarkovProcess_V3HRepair_ContinuousFiniteDenseTimeSet

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal
namespace MarkovProcess.SubMarkovKernelSemigroup
noncomputable section
private theorem finiteDenseApproximation_mem {I : Finset NNReal} (q : I ↪o DenseTime)
    (t : I) :
    DenseTime.castOrderEmbedding (q t) ∈ finiteDenseApproximationPhysicalSet q := by
  rw [finiteDenseApproximationPhysicalSet, denseTimePhysicalSet, Finset.mem_map]
  refine ⟨q t, ?_, rfl⟩
  rw [finiteDenseApproximationIndexSet, Finset.mem_map]
  exact ⟨t, Finset.mem_univ t, rfl⟩
/-- The approximating-set reindexing map is measurable. -/
theorem measurable_finiteDenseApproximationReindex
    {γ : Type*} [MeasurableSpace γ] {I : Finset NNReal} (q : I ↪o DenseTime) :
    Measurable (finiteDenseApproximationReindex (γ := γ) q) := by
  rw [measurable_pi_iff]
  intro t
  let s : finiteDenseApproximationPhysicalSet q :=
    ⟨DenseTime.castOrderEmbedding (q t), finiteDenseApproximation_mem q t⟩
  exact measurable_pi_apply s

namespace IsConservative
variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] [LocallyCompactSpace α] [CompleteSpace α] [StandardBorelSpace α] [Nonempty α]
omit [LocallyCompactSpace α] in
/-- At every finite ordered rational approximation, the continuous-path trajectory has exactly
the transported finite-set kernel law on the fixed original coordinate type. -/
theorem continuousPathTrajectory_map_finiteDenseApproximation
    (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (default : ContinuousPath α)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    {I : Finset NNReal} (q : I ↪o DenseTime) :
    (continuousPathTrajectory P hP default).map
        (ContinuousPath.finiteEvaluation
          (fun t : I ↦ DenseTime.castOrderEmbedding (q t))) =
      finiteDenseApproximationKernel P q := by
  let evalPhysical : ContinuousPath α →
      (finiteDenseApproximationPhysicalSet q → α) :=
    fun path t ↦ path t
  have hevalPhysical : Measurable evalPhysical := by
    rw [measurable_pi_iff]
    intro t
    exact ContinuousPath.measurable_coordinateProcess (alpha := α) t
  have hcomp :
      finiteDenseApproximationReindex (γ := α) q ∘ evalPhysical =
        ContinuousPath.finiteEvaluation
          (fun t : I ↦ DenseTime.castOrderEmbedding (q t)) := by
    rfl
  rw [← hcomp, Kernel.map_comp_right]
  · have hrational := continuousPathTrajectory_map_finiteDenseTimeSet
      P hP default hK (finiteDenseApproximationIndexSet q)
    change (continuousPathTrajectory P hP default).map evalPhysical =
      finiteSetKernel P (finiteDenseApproximationPhysicalSet q) at hrational
    rw [hrational]
    rfl
  · exact hevalPhysical
  · exact measurable_finiteDenseApproximationReindex q

end IsConservative
end
end MarkovProcess.SubMarkovKernelSemigroup


