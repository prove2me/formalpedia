-- Prove2me | Definitions.Def_MarkovProcess_Trajectory_FiniteMarginals
-- name    : MarkovProcess_Trajectory_FiniteMarginals
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T13:28:22.640407+00:00
-- url     : https://prove2.me/theorems/5f09da56-67b1-47e7-99d8-d5de044ec4fd
-- title:
--   MarkovProcess definitions: Trajectory.FiniteMarginals
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.Trajectory.FiniteMarginals`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Trajectory/FiniteMarginals.lean#L1-L194

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_Continuity_DenseTimeContinuousExtension
import Definitions.Def_MarkovProcess_Continuity_DenseTimeContinuousLaw
import Definitions.Def_MarkovProcess_Continuity_DyadicChaining
import Definitions.Def_MarkovProcess_Continuity_DyadicFloor
import Definitions.Def_MarkovProcess_Continuity_DyadicIncrements
import Definitions.Def_MarkovProcess_Continuity_GlobalDyadicFloorModification
import Definitions.Def_MarkovProcess_Continuity_KolmogorovTimeShift
import Definitions.Def_MarkovProcess_Continuity_ShiftedUnitModification
import Definitions.Def_MarkovProcess_DenseTime_ConditionalKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixRecursion
import Definitions.Def_MarkovProcess_DenseTime_Trajectory
import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_FiniteTime_ProjectiveFamily
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Path_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Path_Polish_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_CountableDenseTime
import Definitions.Def_MarkovProcess_Time_DenseTimeHistory
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
import Definitions.Def_MarkovProcess_Trajectory_Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.LocallyFinite

/-!
# Finite rational-time marginals of continuous-path trajectories

This file transports the finite-dimensional laws of the canonical dense-time trajectory to
arbitrary finite sets of nonnegative rational times.  The target coordinates are indexed by the
corresponding finite set of physical `NNReal` times, exactly as in `finiteSetKernel`.

No assertion is made at irrational times or about a Markov, strong Markov, or Hunt property of
the continuous-path law.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

noncomputable section

/-- The finite set of physical nonnegative-real times represented by rational times in `I`. -/
def denseTimePhysicalSet (I : Finset DenseTime) : Finset NNReal :=
  I.map DenseTime.castOrderEmbedding.toEmbedding



private noncomputable def finEquivDenseTimePhysicalPrefix
    (e : ℕ ≃ DenseTime) (n : ℕ) :
    Fin n ≃ denseTimePhysicalPrefix e DenseTime.castOrderEmbedding.toEmbedding n :=
  Equiv.ofBijective
    (fun i ↦
      ⟨DenseTime.castOrderEmbedding (e i), by
        rw [denseTimePhysicalPrefix, Finset.mem_map]
        exact ⟨e i, by
          rw [CountableEnumeration.mem_prefix_iff, e.symm_apply_apply]
          exact i.isLt, rfl⟩⟩)
    ⟨by
      intro i j hij
      apply Fin.ext
      apply e.injective
      apply DenseTime.castOrderEmbedding.injective
      exact congrArg Subtype.val hij,
    by
      intro t
      have ht := t.property
      change t.val ∈ (CountableEnumeration.prefix e n).map
        DenseTime.castOrderEmbedding.toEmbedding at ht
      rw [Finset.mem_map] at ht
      obtain ⟨d, hd, hdt⟩ := ht
      let i : Fin n := ⟨e.symm d, by
        rw [CountableEnumeration.mem_prefix_iff] at hd
        exact hd⟩
      refine ⟨i, Subtype.ext ?_⟩
      change DenseTime.castOrderEmbedding (e i) = t
      rw [show e i = d by exact e.apply_symm_apply d]
      exact hdt⟩

variable {α : Type*}

private def physicalPrefixPathOfFinPath
    (e : ℕ ≃ DenseTime) (n : ℕ) (path : Fin n → α) :
    denseTimePhysicalPrefix e DenseTime.castOrderEmbedding.toEmbedding n → α :=
  fun t ↦ path ((finEquivDenseTimePhysicalPrefix e n).symm t)



namespace IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]





end IsConservative
end
end SubMarkovKernelSemigroup
end MarkovProcess


