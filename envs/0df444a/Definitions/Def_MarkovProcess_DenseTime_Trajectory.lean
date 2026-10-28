-- Prove2me | Definitions.Def_MarkovProcess_DenseTime_Trajectory
-- name    : MarkovProcess_DenseTime_Trajectory
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T13:13:38.092985+00:00
-- url     : https://prove2.me/theorems/80f923c3-f0d0-4a22-b04d-7c68f59e7674
-- title:
--   MarkovProcess definitions: DenseTime.Trajectory
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.DenseTime.Trajectory`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/DenseTime/Trajectory.lean#L1-L353

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_DenseTime_ConditionalKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixRecursion
import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_FiniteTime_ProjectiveFamily
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_CountableDenseTime
import Definitions.Def_MarkovProcess_Time_DenseTimeHistory
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
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

/-!
# Trajectories on countable dense time

This file transports the finite-history transition kernels to the history carrier used by
Mathlib's Ionescu--Tulcea construction, starts the resulting trajectory at a deterministic state,
and reindexes its positive coordinates by a countable dense-time enumeration.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative

noncomputable section

variable {D α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]

/-- Mathlib's locally finite interval and the set interval used by `DenseTimeHistory` give
measurably equivalent history spaces. -/
def denseTimeHistoryMeasurableEquiv (n : ℕ) :
    ((↑(Finset.Iic n) → α) ≃ᵐ DenseTimeHistory α n) :=
  MeasurableEquiv.piCongrLeft (fun _ : Set.Iic n ↦ α) (Equiv.IicFinsetSet n)

/-- The dense-time transition kernel on Mathlib's finite-history carrier. -/
def trajDenseStep (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) : Kernel (↑(Finset.Iic n) → α) α :=
  (denseStep P hP e ι n).comap (denseTimeHistoryMeasurableEquiv n)
    (denseTimeHistoryMeasurableEquiv n).measurable

/-- The transported dense-time transition kernel is Markov. -/
instance isMarkovKernel_trajDenseStep (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    IsMarkovKernel (trajDenseStep P hP e ι n) := by
  rw [trajDenseStep]
  let : IsMarkovKernel (denseStep P hP e ι n) :=
    isMarkovKernel_denseStep P hP e ι n
  infer_instance

/-- The time-zero history determined by an initial state. -/
def initialTrajHistory (x : α) : ↑(Finset.Iic 0) → α :=
  fun _ ↦ x

omit [StandardBorelSpace α] [Nonempty α] in
/-- The deterministic time-zero history is a measurable function of its initial state. -/
theorem measurable_initialTrajHistory : Measurable (initialTrajHistory (α := α)) := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_id

/-- The deterministic kernel from an initial state to its time-zero history. -/
def initialTrajHistoryKernel : Kernel α (↑(Finset.Iic 0) → α) :=
  Kernel.deterministic initialTrajHistory measurable_initialTrajHistory

/-- Remove the augmented initial-state coordinate from a natural-number trajectory. -/
def dropInitialTrajCoordinate (path : ℕ → α) : ℕ → α :=
  fun n ↦ path (n + 1)

omit [StandardBorelSpace α] [Nonempty α] in
/-- Dropping the initial trajectory coordinate is measurable. -/
theorem measurable_dropInitialTrajCoordinate :
    Measurable (dropInitialTrajCoordinate (α := α)) := by
  rw [measurable_pi_iff]
  intro n
  exact measurable_pi_apply (n + 1)

/-- The countable trajectory in enumeration order, with coordinate zero corresponding to the
first observation rather than the augmented initial state. -/
def enumeratedDenseTimeTrajectory (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) : Kernel α (ℕ → α) :=
  ((Kernel.traj (X := fun _ ↦ α) (trajDenseStep P hP e ι) 0).comap
      initialTrajHistory measurable_initialTrajHistory).map dropInitialTrajCoordinate

/-- The trajectory in enumeration order is a Markov kernel. -/
instance isMarkovKernel_enumeratedDenseTimeTrajectory (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) :
    IsMarkovKernel (enumeratedDenseTimeTrajectory P hP e ι) := by
  rw [enumeratedDenseTimeTrajectory]
  exact Kernel.IsMarkovKernel.map _ measurable_dropInitialTrajCoordinate

/-- Reindex the enumerated trajectory by its dense-time labels. -/
def denseTimeTrajectory (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) : Kernel α (D → α) :=
  (enumeratedDenseTimeTrajectory P hP e ι).map
    (CountableEnumeration.measurableEquivPath e α)

/-- The dense-time trajectory is a Markov kernel. -/
instance isMarkovKernel_denseTimeTrajectory (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) :
    IsMarkovKernel (denseTimeTrajectory P hP e ι) := by
  rw [denseTimeTrajectory]
  exact Kernel.IsMarkovKernel.map _
    (CountableEnumeration.measurableEquivPath e α).measurable



private def rawTrajAppend (n : ℕ) :
    ((↑(Finset.Iic n) → α) × α) → (↑(Finset.Iic (n + 1)) → α) :=
  IicProdIoc (X := fun _ ↦ α) n (n + 1) ∘
    Prod.map id (MeasurableEquiv.piSingleton (X := fun _ ↦ α) n)









/-- Restrict an enumeration-ordered trajectory to its first `n` observations. -/
def enumeratedDenseTimePrefix (n : ℕ) (path : ℕ → α) : Fin n → α :=
  fun i ↦ path i







/-- Restrict a dense-time-labelled trajectory to the first `n` labels of an enumeration. -/
def denseTimeTrajectoryPrefix (e : ℕ ≃ D) (n : ℕ) (path : D → α) : Fin n → α :=
  fun i ↦ path (e i)







end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess


