-- Prove2me | Definitions.Def_MarkovProcess_V3H_DenseTime_PhysicalReindex_4ed652de
-- name    : MarkovProcess_V3H_DenseTime_PhysicalReindex_4ed652de
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:57:07.045026+00:00
-- url     : https://prove2.me/theorems/6bbc19f1-52c1-4b7c-9c19-45b0e9647597
-- title:
--   MarkovProcess: MarkovProcess_V3H_DenseTime_PhysicalReindex_4ed652de
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
import Definitions.Def_MarkovProcess_V3H_Trajectory_FiniteMarginals_a8fbfae5
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

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

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

@[simp]
theorem physicalSetEquiv_apply (I : Finset DenseTime) (t : I) :
    (physicalSetEquiv I t : NNReal) = castOrderEmbedding t := rfl

end DenseTime

namespace DenseTimePath

open SubMarkovKernelSemigroup

variable {alpha : Type*}

/-- Reindex a finite path labelled by physical rational times back to dense-time labels. -/
def pullbackPhysicalSet (I : Finset DenseTime)
    (path : denseTimePhysicalSet I → alpha) : I → alpha :=
  fun t ↦ path (DenseTime.physicalSetEquiv I t)

@[simp]
theorem p2m_embedded_1b3a31dbc57a572b (I : Finset DenseTime)
    (path : denseTimePhysicalSet I → alpha) (t : I) :
    pullbackPhysicalSet I path t = path (DenseTime.physicalSetEquiv I t) := rfl

variable [MeasurableSpace alpha]

/-- Reindexing a finite physical-time path by its dense labels is measurable. -/
theorem measurable_pullbackPhysicalSet (I : Finset DenseTime) :
    Measurable (pullbackPhysicalSet (alpha := alpha) I) := by
  rw [measurable_pi_iff]
  intro t
  exact measurable_pi_apply (DenseTime.physicalSetEquiv I t)

omit [MeasurableSpace alpha] in
/-- Evaluating a continuous path on physical rational times and reindexing gives restriction of
its dense-time path. -/
theorem pullbackPhysicalSet_evaluation (I : Finset DenseTime)
    [TopologicalSpace alpha] (omega : ContinuousPath alpha) :
    pullbackPhysicalSet I
        (fun t : denseTimePhysicalSet I ↦ omega t) =
      I.restrict (ContinuousPath.denseRestriction omega) := by
  funext t
  rfl

end DenseTimePath
end
end MarkovProcess


