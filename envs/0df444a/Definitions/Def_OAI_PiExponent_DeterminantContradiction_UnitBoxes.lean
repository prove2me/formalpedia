-- Prove2me | Definitions.Def_OAI_PiExponent_DeterminantContradiction_UnitBoxes
-- name    : OAI_PiExponent_DeterminantContradiction_UnitBoxes
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-23T10:10:47.084002+00:00
-- url     : https://prove2.me/theorems/50c5bfd8-befa-4434-8032-9b264253c767
-- title:
--   Translated half-open unit boxes and their finite union
-- statement:
--   Defines the half-open unit box based at a natural-valued vector and the union of such boxes over a finite set.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators
noncomputable section
namespace OAI.PiExponent.DeterminantContradiction

def unitBox {n : ℕ} (a : Fin n → ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, (a i : ℝ) ≤ x i ∧ x i < (a i : ℝ) + 1}

def unitBoxUnion {n : ℕ} (S : Finset (Fin n → ℕ)) : Set (Fin n → ℝ) :=
  ⋃ a ∈ (S : Set (Fin n → ℕ)), unitBox a

end OAI.PiExponent.DeterminantContradiction


