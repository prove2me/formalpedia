-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_ExistsDenseTimeSequence
-- name    : MarkovProcess_V3HRepair_ExistsDenseTimeSequence
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T09:48:27.171762+00:00
-- url     : https://prove2.me/theorems/71d1f210-7c21-4688-a868-b71b58d52097
-- title:
--   Verified MarkovProcess source repair: ExistsDenseTimeSequence
-- statement:
--   For every finite ordered collection of nonnegative real times, construct compatible strictly ordered dense rational-time approximations converging coordinatewise.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream commit 1f8060caa137731fa08029592019eeaf9d997fe5; source-faithful adapted proof module V3HRepaired.ExistsDenseTimeSequence, archived SHA-256 035e1e0e28acb74c3490c4bd0ec1d0d5073aa9ba18d3d5118a28826bd2a68623.

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

/-- Nonnegative rational times admit a sequence converging to every nonnegative real time. -/
private theorem exists_denseTime_seq_tendsto (t : NNReal) :
    ∃ q : ℕ → DenseTime,
      Tendsto (fun n ↦ DenseTime.castOrderEmbedding (q n)) atTop (nhds t) := by
  obtain ⟨q, _, _, hq⟩ := ContinuousPath.denseRange_castOrderEmbedding
    |>.exists_seq_strictAnti_tendsto
    DenseTime.castOrderEmbedding.monotone t
  exact ⟨q, by simpa only [Function.comp_apply] using! hq⟩








namespace ContinuousPath







end ContinuousPath

section KernelLimits

variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] [LocallyCompactSpace α]







namespace SubMarkovKernelSemigroup













namespace IsConservative

variable [CompleteSpace α] [StandardBorelSpace α] [Nonempty α]





end IsConservative
end SubMarkovKernelSemigroup

end KernelLimits

end
end MarkovProcess


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




open MarkovProcess in
theorem MarkovProcess.exists_denseTime_finiteOrderEmbedding_seq_tendsto
    {ι : Type*} [Finite ι] [LinearOrder ι] (times : ι ↪o NNReal) :
    ∃ q : ℕ → ι ↪o DenseTime,
      ∀ i, Tendsto (fun k ↦ DenseTime.castOrderEmbedding (q k i))
        atTop (nhds (times i)) := by
  choose q hq using fun i : ι ↦ exists_denseTime_seq_tendsto (times i)
  have hordered : ∀ᶠ k in atTop,
      ∀ i j : ι, i < j →
        DenseTime.castOrderEmbedding (q i k) <
          DenseTime.castOrderEmbedding (q j k) := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    by_cases hij : i < j
    · exact ((hq i).eventually_lt (hq j) (times.strictMono hij)).mono
        fun k hk _ ↦ hk
    · exact Filter.Eventually.of_forall fun _ hij' ↦ (hij hij').elim
  rw [Filter.eventually_atTop] at hordered
  obtain ⟨N, hN⟩ := hordered
  let qOrdered : ℕ → ι ↪o DenseTime := fun k ↦
    OrderEmbedding.ofStrictMono (fun i ↦ q i (k + N)) fun i j hij ↦ by
      apply DenseTime.castOrderEmbedding.lt_iff_lt.mp
      exact hN (k + N) (Nat.le_add_left N k) i j hij
  refine ⟨qOrdered, fun i ↦ ?_⟩
  have hshift := (hq i).comp (Filter.tendsto_add_atTop_nat N)
  simpa only [qOrdered, Function.comp_apply] using! hshift


