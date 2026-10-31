-- Prove2me | Definitions.Def_MarkovProcess_V3H_Parameterized_OrderedGrid_cb0f8631
-- name    : MarkovProcess_V3H_Parameterized_OrderedGrid_cb0f8631
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:35:09.814899+00:00
-- url     : https://prove2.me/theorems/bbd87538-485e-42a5-a0cc-160a559f8ab0
-- title:
--   MarkovProcess: MarkovProcess_V3H_Parameterized_OrderedGrid_cb0f8631
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Parameterized_Semigroup_5f8b28ce
import Definitions.Def_MarkovProcess_V3H_Time_OrderedGrid_1c9977ee
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Parameterized trajectory laws on a fixed ordered time grid

This file constructs a jointly measurable kernel from a parameter and starting state to the
discrete trajectory on one fixed ordered grid. The parameter is carried as a deterministic
component of an augmented state through the Ionescu--Tulcea construction, then removed from the
output path.

The result is a path-law kernel on `Theta × alpha` with values in measures on `ℕ → alpha`.
It is not a continuous-time path law and does not assert measurability in the grid.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ProbabilityTheory

namespace MarkovProcess

namespace ParameterizedSubMarkovKernelSemigroup

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)

private def lastIndex (n : ℕ) : Finset.Iic n :=
  ⟨n, Finset.mem_Iic.mpr le_rfl⟩

/-- The jointly measurable transition kernel at one fixed time increment. -/
def parameterStateKernel (t : NNReal) : Kernel (Theta × alpha) alpha :=
  P.jointKernel.comap (fun q : Theta × alpha ↦ (q.1, (t, q.2)))
    (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))

@[simp]
theorem parameterStateKernel_apply (t : NNReal) (theta : Theta) (x : alpha) :
    P.parameterStateKernel t (theta, x) = P theta t x :=
  rfl

/-- The augmented transition preserves the parameter deterministically and samples the state. -/
noncomputable def augmentedKernel (t : NNReal) : Kernel (Theta × alpha) (Theta × alpha) :=
  Kernel.deterministic Prod.fst measurable_fst ×ₖ P.parameterStateKernel t

/-- Pointwise conservativity makes each augmented transition a Markov kernel. -/
theorem isMarkovKernel_augmentedKernel
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative) (t : NNReal) :
    IsMarkovKernel (P.augmentedKernel t) := by
  let : IsMarkovKernel (P.parameterStateKernel t) :=
    ⟨fun q ↦ by
      rw [parameterStateKernel_apply]
      exact ⟨hP q.1 t q.2⟩⟩
  rw [augmentedKernel]
  infer_instance

/-- The history-dependent augmented step kernel on a fixed ordered grid. -/
noncomputable def parameterizedOrderedGridStepKernel (grid : OrderedGrid) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → Theta × alpha) (Theta × alpha) :=
  (P.augmentedKernel (grid.increment n)).comap
    (fun history ↦ history (lastIndex n))
    (measurable_pi_apply (lastIndex n))

/-- Every augmented ordered-grid step is a Markov kernel under pointwise conservativity. -/
theorem isMarkovKernel_parameterizedOrderedGridStepKernel
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (grid : OrderedGrid) (n : ℕ) :
    IsMarkovKernel (P.parameterizedOrderedGridStepKernel grid n) := by
  let : IsMarkovKernel (P.augmentedKernel (grid.increment n)) :=
    P.isMarkovKernel_augmentedKernel hP (grid.increment n)
  rw [parameterizedOrderedGridStepKernel]
  infer_instance

/-- The jointly measurable path-law kernel from parameter and starting state to trajectories on
one fixed ordered grid. -/
noncomputable def parameterizedOrderedGridTrajectoryKernel
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (grid : OrderedGrid) : Kernel (Theta × alpha) (ℕ → alpha) := by
  letI (n : ℕ) : IsMarkovKernel (P.parameterizedOrderedGridStepKernel grid n) :=
    P.isMarkovKernel_parameterizedOrderedGridStepKernel hP grid n
  exact ((Kernel.traj (P.parameterizedOrderedGridStepKernel grid) 0).comap
    (fun q ↦ initialHistory q) measurable_initialHistory).map
      (fun path : ℕ → Theta × alpha ↦ fun n ↦ (path n).2)





end ParameterizedSubMarkovKernelSemigroup

end MarkovProcess


