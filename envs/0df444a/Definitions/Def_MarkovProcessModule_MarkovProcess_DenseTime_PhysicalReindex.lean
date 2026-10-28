-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_DenseTime_PhysicalReindex
-- name    : MarkovProcessModule_MarkovProcess_DenseTime_PhysicalReindex
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T20:46:55.093987+00:00
-- url     : https://prove2.me/theorems/ae247649-ec94-49b2-9cc9-650b9f1e7634
-- title:
--   MarkovProcess.DenseTime.PhysicalReindex
-- statement:
--   # Reindexing finite rational coordinates by physical time
--
--   A finite set of dense rational times is canonically equivalent to its image in `NNReal`.  This
--   file records the induced measurable path reindexing and its compatibility with continuous-path
--   evaluation.  No probability-law or Markov claim is made.
--
--   Complete pinned Lean module MarkovProcess.DenseTime.PhysicalReindex by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/DenseTime/PhysicalReindex.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Trajectory_FiniteMarginals

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
theorem pullbackPhysicalSet_apply (I : Finset DenseTime)
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


