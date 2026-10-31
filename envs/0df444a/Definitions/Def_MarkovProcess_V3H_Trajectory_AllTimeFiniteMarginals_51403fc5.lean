-- Prove2me | Definitions.Def_MarkovProcess_V3H_Trajectory_AllTimeFiniteMarginals_51403fc5
-- name    : MarkovProcess_V3H_Trajectory_AllTimeFiniteMarginals_51403fc5
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:57:06.190408+00:00
-- url     : https://prove2.me/theorems/a5391015-65f0-4480-8419-9b8aa67d42f9
-- title:
--   MarkovProcess: MarkovProcess_V3H_Trajectory_AllTimeFiniteMarginals_51403fc5
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Feller_Semigroup_2cfe612a
import Definitions.Def_MarkovProcess_V3H_FiniteTime_ProjectiveFamily_1eff0efa
import Definitions.Def_MarkovProcess_V3H_Kernel_C0SemigroupJoint_9aea0383
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMeasure_354455bb
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
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

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Arbitrary-time finite marginals of continuous-path trajectories

This file develops the simultaneous rational approximation needed to pass from the already
identified rational finite-dimensional distributions to finite families of arbitrary
nonnegative real times.  It proves the path-side dominated-convergence argument, identifies every
rational approximating law with the existing finite-set kernel, and reduces the desired equality
to compactly-supported-test convergence of those finite-set kernels.

The remaining Feller analytic statement is not claimed here: one must still prove that the
recursively composed finite-time kernels have that convergence under simultaneous convergence of
their strictly ordered time coordinates.  No continuous-time Markov or Hunt property is assumed
or asserted.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal

namespace MarkovProcess

noncomputable section







namespace ContinuousPath

/-- Evaluate a continuous path at a finite family of times. -/
def finiteEvaluation {ι α : Type*} [TopologicalSpace α]
    (τ : ι → NNReal) : ContinuousPath α → (ι → α) :=
  fun path i ↦ path (τ i)

/-- Simultaneous evaluation at finitely many fixed times is continuous in the path. -/
theorem continuous_finiteEvaluation {ι α : Type*} [Finite ι]
    [TopologicalSpace α] (τ : ι → NNReal) :
    Continuous (finiteEvaluation (α := α) τ) := by
  apply continuous_pi
  intro i
  exact continuous_eval (alpha := α) (τ i)



end ContinuousPath

section KernelLimits

variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] [LocallyCompactSpace α]







namespace SubMarkovKernelSemigroup

/-- The rational index set used by one finite ordered rational approximation. -/
def finiteDenseApproximationIndexSet {I : Finset NNReal} (q : I ↪o DenseTime) :
    Finset DenseTime :=
  Finset.univ.map q.toEmbedding

/-- The corresponding finite set of physical nonnegative-real times. -/
def finiteDenseApproximationPhysicalSet {I : Finset NNReal} (q : I ↪o DenseTime) :
    Finset NNReal :=
  denseTimePhysicalSet (finiteDenseApproximationIndexSet q)

private theorem finiteDenseApproximation_mem {I : Finset NNReal} (q : I ↪o DenseTime)
    (t : I) :
    DenseTime.castOrderEmbedding (q t) ∈ finiteDenseApproximationPhysicalSet q := by
  rw [finiteDenseApproximationPhysicalSet, denseTimePhysicalSet, Finset.mem_map]
  refine ⟨q t, ?_, rfl⟩
  rw [finiteDenseApproximationIndexSet, Finset.mem_map]
  exact ⟨t, Finset.mem_univ t, rfl⟩

/-- Reindex a path on an approximating physical-time set by the original finite set. -/
def finiteDenseApproximationReindex {γ : Type*} {I : Finset NNReal}
    (q : I ↪o DenseTime) :
    (finiteDenseApproximationPhysicalSet q → γ) → I → γ :=
  fun path t ↦ path ⟨DenseTime.castOrderEmbedding (q t),
    finiteDenseApproximation_mem q t⟩



/-- The candidate finite law at one rational approximation, transported back to the fixed
coordinate type indexed by the original time set. -/
noncomputable def finiteDenseApproximationKernel
    (P : SubMarkovKernelSemigroup α) {I : Finset NNReal} (q : I ↪o DenseTime) :
    Kernel α (I → α) :=
  (finiteSetKernel P (finiteDenseApproximationPhysicalSet q)).map
    (finiteDenseApproximationReindex q)

namespace IsConservative

variable [CompleteSpace α] [StandardBorelSpace α] [Nonempty α]





end IsConservative
end SubMarkovKernelSemigroup

end KernelLimits

end
end MarkovProcess


