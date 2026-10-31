-- Prove2me | Definitions.Def_MarkovProcess_V3H_DenseTime_TrajectoryMarginals_db9e38cc
-- name    : MarkovProcess_V3H_DenseTime_TrajectoryMarginals_db9e38cc
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:47:25.768068+00:00
-- url     : https://prove2.me/theorems/ce2350aa-9838-47e5-85be-40a1d1ea114d
-- title:
--   MarkovProcess: MarkovProcess_V3H_DenseTime_TrajectoryMarginals_db9e38cc
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_PrefixKernel_a192bbea
import Definitions.Def_MarkovProcess_V3H_DenseTime_Trajectory_b0f7f66f
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelRestriction_041bf9e5
import Definitions.Def_MarkovProcess_V3H_FiniteTime_Kernel_7ce8d73d
import Definitions.Def_MarkovProcess_V3H_FiniteTime_ProjectiveFamily_1eff0efa
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
import Definitions.Def_MarkovProcess_V3H_Time_FiniteOrderedTimes_717796dd
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# One-time marginals of the dense-time trajectory

This file identifies every coordinate marginal of the dense-time trajectory kernel with the
corresponding transition kernel.  The result is derived from the exact finite-prefix identity.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative

noncomputable section

variable {D α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]

omit [StandardBorelSpace α] [Nonempty α] in
private theorem finiteTimeKernel_map_eval
    (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    {n : ℕ} (times : FiniteOrderedTimes n) (i : Fin n) :
    (finiteTimeKernel P times).map (fun path ↦ path i) = P (times i) := by
  let select : Fin 1 ↪o Fin n :=
    { toFun := fun _ ↦ i
      inj' := fun a b _ ↦ Subsingleton.elim a b
      map_rel_iff' := by
        intro a b
        constructor
        · intro _
          rw [Subsingleton.elim a b]
        · intro _
          exact le_rfl }
  have hfun :
      (fun path : Fin 1 → α ↦ path 0) ∘ FiniteOrderedTimes.restrictPath select =
        fun path : Fin n → α ↦ path i := by
    funext path
    rfl
  rw [← hfun, Kernel.map_comp_right]
  · rw [hP.p2m_embedded_df60a2ab25853e30 P times select]
    simpa only using! _root_.MarkovProcess.SubMarkovKernelSemigroup.p2m_embedded_5bab9ee57d353238 P (times.restrict select)
  · exact FiniteOrderedTimes.measurable_restrictPath select
  · exact measurable_pi_apply 0

/-- Every coordinate marginal of the dense-time trajectory is the transition kernel at its
embedded physical time. -/
theorem p2m_embedded_b6cde874390934be
    (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) (d : D) :
    (denseTimeTrajectory P hP e ι).map (fun path ↦ path d) = P (ι d) := by
  let k : ℕ := e.symm d
  let i : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  have hcoord : e i = d := by
    change e (e.symm d) = d
    exact e.apply_symm_apply d
  have hfun :
      (fun path : Fin (k + 1) → α ↦ path i) ∘
          denseTimeTrajectoryPrefix e (k + 1) =
        fun path : D → α ↦ path d := by
    funext path
    change path (e i) = path d
    rw [hcoord]
  rw [← hfun, Kernel.map_comp_right]
  · rw [denseTimeTrajectory_map_prefix P hP e ι (k + 1)]
    rw [denseTimePrefixKernel_eq_map, ← Kernel.map_comp_right]
    · have ht : ι (e i) ∈ denseTimePhysicalPrefix e ι (k + 1) := by
        rw [denseTimePhysicalPrefix, Finset.mem_map]
        refine ⟨e i, ?_, rfl⟩
        rw [CountableEnumeration.mem_prefix_iff, e.symm_apply_apply]
        exact i.isLt
      let t : denseTimePhysicalPrefix e ι (k + 1) := ⟨ι (e i), ht⟩
      have hprefix :
          (fun path : Fin (k + 1) → α ↦ path i) ∘
              denseTimePrefixReindex e ι (k + 1) =
            fun path : denseTimePhysicalPrefix e ι (k + 1) → α ↦ path t := by
        rfl
      rw [hprefix, finiteSetKernel_eq_map, ← Kernel.map_comp_right]
      · let j : Fin (denseTimePhysicalPrefix e ι (k + 1)).card :=
          ((denseTimePhysicalPrefix e ι (k + 1)).orderIsoOfFin rfl).symm t
        have hordered :
            (fun path : denseTimePhysicalPrefix e ι (k + 1) → α ↦ path t) ∘
                orderedPathToFiniteSet (denseTimePhysicalPrefix e ι (k + 1)) =
              fun path : Fin (denseTimePhysicalPrefix e ι (k + 1)).card → α ↦ path j := by
          rfl
        rw [hordered, finiteTimeKernel_map_eval P hP _ j]
        have hjtime :
            finiteSetTimes (denseTimePhysicalPrefix e ι (k + 1)) j = ι (e i) := by
          change ((((denseTimePhysicalPrefix e ι (k + 1)).orderIsoOfFin rfl) j :
            denseTimePhysicalPrefix e ι (k + 1)) : NNReal) = ι (e i)
          dsimp only [j]
          rw [OrderIso.apply_symm_apply]
        rw [hjtime, hcoord]
      · exact measurable_orderedPathToFiniteSet
          (denseTimePhysicalPrefix e ι (k + 1))
      · exact measurable_pi_apply t
    · exact measurable_denseTimePrefixReindex e ι (k + 1)
    · fun_prop
  · exact measurable_denseTimeTrajectoryPrefix e (k + 1)
  · fun_prop

end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess


