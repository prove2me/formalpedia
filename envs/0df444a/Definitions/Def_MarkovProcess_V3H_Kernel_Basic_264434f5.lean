-- Prove2me | Definitions.Def_MarkovProcess_V3H_Kernel_Basic_264434f5
-- name    : MarkovProcess_V3H_Kernel_Basic_264434f5
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:14:25.269386+00:00
-- url     : https://prove2.me/theorems/830c19ed-7a84-4b32-8c4f-a572a94dfae2
-- title:
--   MarkovProcess: MarkovProcess_V3H_Kernel_Basic_264434f5
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Mathlib.Probability.Kernel.Composition.Comp

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Sub-Markov kernels

This file records the elementary mass algebra of sub-Markov kernels.  It does
not define transition families or connect kernels to operator semigroups or
stochastic processes.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace MarkovProcess

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- A kernel is sub-Markov if each of its measures has total mass at most one. -/
def IsSubMarkovKernel (κ : ProbabilityTheory.Kernel α β) : Prop :=
  ∀ x, κ x Set.univ ≤ 1

namespace IsSubMarkovKernel

open ProbabilityTheory

variable {κ : Kernel α β} {η : Kernel β γ}

/-- A sub-Markov kernel assigns mass at most one to every set. -/
theorem measure_le_one (hκ : IsSubMarkovKernel κ) (x : α) (s : Set β) : κ x s ≤ 1 :=
  (measure_mono (Set.subset_univ s)).trans (hκ x)

/-- The uniform Mathlib kernel bound of a sub-Markov kernel is at most one. -/
theorem bound_le_one (hκ : IsSubMarkovKernel κ) : κ.bound ≤ 1 := by
  apply iSup_le
  exact hκ

/-- A sub-Markov kernel is a finite kernel. -/
theorem isFiniteKernel (hκ : IsSubMarkovKernel κ) : IsFiniteKernel κ :=
  ⟨⟨1, ENNReal.one_lt_top, hκ⟩⟩



/-- The identity kernel is sub-Markov. -/
theorem id : IsSubMarkovKernel (Kernel.id : Kernel α α) := by
  intro x
  rw [Kernel.id_apply]
  exact le_of_eq measure_univ

/-- Every Markov kernel is sub-Markov. -/
theorem of_isMarkovKernel (κ : Kernel α β) [IsMarkovKernel κ] : IsSubMarkovKernel κ := by
  intro x
  exact le_of_eq measure_univ

/-- The composition of two sub-Markov kernels is sub-Markov. -/
theorem comp (hη : IsSubMarkovKernel η) (hκ : IsSubMarkovKernel κ) :
    IsSubMarkovKernel (η ∘ₖ κ) := by
  intro x
  calc
    (η ∘ₖ κ) x Set.univ ≤ κ x Set.univ * η.bound :=
      Kernel.comp_apply_univ_le κ η x
    _ ≤ 1 * 1 := mul_le_mul' (hκ x) hη.bound_le_one
    _ = 1 := one_mul 1

end IsSubMarkovKernel

end MarkovProcess


