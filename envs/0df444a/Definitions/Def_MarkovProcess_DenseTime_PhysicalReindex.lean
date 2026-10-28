-- Prove2me | Definitions.Def_MarkovProcess_DenseTime_PhysicalReindex
-- name    : MarkovProcess_DenseTime_PhysicalReindex
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T13:34:36.487646+00:00
-- url     : https://prove2.me/theorems/a2cb59be-f4e3-4216-a07a-1c7e3bd2cc29
-- title:
--   MarkovProcess definitions: DenseTime.PhysicalReindex
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.DenseTime.PhysicalReindex`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/DenseTime/PhysicalReindex.lean#L1-L86

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
import Definitions.Def_MarkovProcess_Trajectory_FiniteMarginals
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
# Reindexing finite rational coordinates by physical time

A finite set of dense rational times is canonically equivalent to its image in `NNReal`.  This
file records the induced measurable path reindexing and its compatibility with continuous-path
evaluation.  No probability-law or Markov claim is made.
-/

namespace MarkovProcess

noncomputable section

namespace DenseTime

open SubMarkovKernelSemigroup

/-- Casting identifies a finite dense-time set with its image in physical nonnegative-real time. -/
def physicalSetEquiv (I : Finset DenseTime) : I ≃ denseTimePhysicalSet I :=
  Equiv.ofBijective
    (fun t ↦ ⟨castOrderEmbedding t, by
      rw [denseTimePhysicalSet, Finset.mem_map]
      exact ⟨t, t.property, rfl⟩⟩)
    ⟨by
      intro t u h
      apply Subtype.ext
      exact castOrderEmbedding.injective (congrArg Subtype.val h),
    by
      intro t
      have ht := t.property
      change t.val ∈ I.map castOrderEmbedding.toEmbedding at ht
      rw [Finset.mem_map] at ht
      obtain ⟨r, hrI, hrt⟩ := ht
      exact ⟨⟨r, hrI⟩, Subtype.ext hrt⟩⟩



end DenseTime

namespace DenseTimePath

open SubMarkovKernelSemigroup

variable {alpha : Type*}

/-- Reindex a finite path labelled by physical rational times back to dense-time labels. -/
def pullbackPhysicalSet (I : Finset DenseTime)
    (path : denseTimePhysicalSet I → alpha) : I → alpha :=
  fun t ↦ path (DenseTime.physicalSetEquiv I t)



variable [MeasurableSpace alpha]





end DenseTimePath
end
end MarkovProcess


