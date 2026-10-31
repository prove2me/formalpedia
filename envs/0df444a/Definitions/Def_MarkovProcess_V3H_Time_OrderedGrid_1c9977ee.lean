-- Prove2me | Definitions.Def_MarkovProcess_V3H_Time_OrderedGrid_1c9977ee
-- name    : MarkovProcess_V3H_Time_OrderedGrid_1c9977ee
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:32:34.956315+00:00
-- url     : https://prove2.me/theorems/aaf75439-9ee0-45ad-83ca-3f25db199509
-- title:
--   MarkovProcess: MarkovProcess_V3H_Time_OrderedGrid_1c9977ee
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Trajectory laws on a fixed ordered time grid

This file applies the Ionescu--Tulcea theorem to a conservative sub-Markov
kernel semigroup on one fixed nondecreasing `NNReal`-valued time grid.  The
result is only a discrete trajectory law on `ℕ → α` for that grid.
-/

open MeasureTheory
open ProbabilityTheory

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]

/-- A fixed nondecreasing grid of nonnegative times. -/
structure OrderedGrid where
  /-- The time assigned to each discrete index. -/
  time : ℕ → NNReal
  /-- Grid times are nondecreasing. -/
  monotone_time : Monotone time

namespace OrderedGrid

/-- The time increment from index `n` to index `n + 1`. -/
def increment (grid : OrderedGrid) (n : ℕ) : NNReal :=
  grid.time (n + 1) - grid.time n

end OrderedGrid

/-- The singleton history at index zero determined by a starting state. -/
def initialHistory (x : α) : (i : Finset.Iic 0) → α :=
  fun _ => x

/-- The singleton-history map is measurable. -/
theorem measurable_initialHistory : Measurable (initialHistory : α → (i : Finset.Iic 0) → α) :=
  measurable_pi_iff.mpr fun _ => measurable_id

namespace SubMarkovKernelSemigroup

variable (P : SubMarkovKernelSemigroup α)

private def lastIndex (n : ℕ) : Finset.Iic n :=
  ⟨n, Finset.mem_Iic.mpr le_rfl⟩

/-- The history-dependent Ionescu--Tulcea step kernel on `grid`.

Only the current state, the last coordinate of the supplied history, is used.
-/
def orderedGridStepKernel (grid : OrderedGrid) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → α) α :=
  (P (grid.increment n)).comap
    (fun history => history (lastIndex n))
    (measurable_pi_apply (lastIndex n))

/-- Conservativity makes every ordered-grid step kernel a Markov kernel. -/
theorem IsConservative.isMarkovKernel_orderedGridStepKernel
    (hP : P.IsConservative) (grid : OrderedGrid) (n : ℕ) :
    IsMarkovKernel (orderedGridStepKernel P grid n) := by
  let : IsMarkovKernel (P (grid.increment n)) := hP.isMarkovKernel (grid.increment n)
  rw [orderedGridStepKernel]
  infer_instance

/-- The Ionescu--Tulcea kernel from a starting state to trajectories on one
fixed ordered grid. -/
noncomputable def orderedGridTrajectoryKernel
    (hP : P.IsConservative) (grid : OrderedGrid) : Kernel α (ℕ → α) := by
  letI (n : ℕ) : IsMarkovKernel (orderedGridStepKernel P grid n) :=
    IsConservative.isMarkovKernel_orderedGridStepKernel P hP grid n
  exact (Kernel.traj (orderedGridStepKernel P grid) 0).comap
    initialHistory measurable_initialHistory



/-- The trajectory law on one fixed ordered grid, started from `x`. -/
noncomputable def orderedGridTrajectoryLaw
    (hP : P.IsConservative) (grid : OrderedGrid) (x : α) : Measure (ℕ → α) :=
  orderedGridTrajectoryKernel P hP grid x







end SubMarkovKernelSemigroup

end MarkovProcess


