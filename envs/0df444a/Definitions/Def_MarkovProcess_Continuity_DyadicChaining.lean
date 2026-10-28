-- Prove2me | Definitions.Def_MarkovProcess_Continuity_DyadicChaining
-- name    : MarkovProcess_Continuity_DyadicChaining
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T12:42:09.224376+00:00
-- url     : https://prove2.me/theorems/e1506996-c816-4d35-8a0c-badae0726130
-- title:
--   MarkovProcess definitions: Continuity.DyadicChaining
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.Continuity.DyadicChaining`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/DyadicChaining.lean#L1-L345

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_Continuity_DyadicIncrements
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Kolmogorov

/-!
# Chaining across unit dyadic grids

This file merges the following former modules, one section each:

* `DyadicGridChaining`: Same-level chaining on dyadic grids
* `DyadicMultiscale`: Refinement and parent comparison for unit dyadic grids
* `DyadicAncestorChaining`: Finite chains of dyadic ancestors
* `DyadicAncestorTail`: Uniform tail bounds for finite dyadic ancestor chains
-/

namespace MarkovProcess

section DyadicGridChaining

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]





end DyadicGridChaining

section DyadicMultiscale

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

/-- The canonical inclusion of the level-`n` unit dyadic grid into level `n + 1`.
Its value is twice the old grid index. -/
def unitDyadicRefineIndex (n : ℕ) (i : Fin (2 ^ n + 1)) : Fin (2 ^ (n + 1) + 1) :=
  ⟨2 * i.val, by
    have hi : i.val ≤ 2 ^ n := Nat.le_of_lt_succ i.isLt
    rw [pow_succ]
    omega⟩





/-- The canonical level-`n` parent of a point on the level-`n + 1` unit dyadic grid.
It is obtained by rounding the fine-grid index down after division by two. -/
def unitDyadicParentIndex (n : ℕ) (i : Fin (2 ^ (n + 1) + 1)) : Fin (2 ^ n + 1) :=
  ⟨i.val / 2, by
    have hi : i.val ≤ 2 ^ (n + 1) := Nat.le_of_lt_succ i.isLt
    have hi' : i.val ≤ 2 ^ n * 2 := by simpa only [pow_succ] using hi
    omega⟩













end DyadicMultiscale

section DyadicAncestorChaining

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

/-- The canonical level-`n` ancestor of a point lying `r` dyadic refinements above it. -/
def unitDyadicAncestorIndex (n : ℕ) :
    (r : ℕ) → Fin (2 ^ (n + r) + 1) → Fin (2 ^ n + 1)
  | 0, i => i
  | r + 1, i =>
      unitDyadicAncestorIndex n r (unitDyadicParentIndex (n + r) i)









end DyadicAncestorChaining

section DyadicAncestorTail

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]







end DyadicAncestorTail

end MarkovProcess


