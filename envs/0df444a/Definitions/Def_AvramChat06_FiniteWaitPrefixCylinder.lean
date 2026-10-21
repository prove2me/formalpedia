-- Prove2me | Definitions.Def_AvramChat06_FiniteWaitPrefixCylinder
-- name    : AvramChat06_FiniteWaitPrefixCylinder
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-20T15:59:45.807985+00:00
-- url     : https://prove2.me/theorems/9379b866-b6fd-4580-b0c3-3886a6270fe0
-- title:
--   Finite waiting-time padding and adjacent arrival cylinder
-- statement:
--   Reusable pinned Lean declarations underlying the Chat 06 verified Poisson waiting-time and finite observation cylinders. Imported by subsequent theorem proof targets without locally redeclaring definitions in their preambles.
-- source:
--   Chat 06 verified local definitions extracted verbatim from bv_two_arrival_thresholds_finite_prefix_cylinder_chat06_20261020.lean.

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Data.Fin.Basic

open MeasureTheory Set

namespace AvramChat06

def padWaitPrefix (n : ℕ) (g : Fin (n + 2) → ℝ) (i : ℕ) : ℝ :=
  if h : i < n + 2 then g ⟨i, h⟩ else 0

def positiveCountPrefixEvent (n : ℕ) (t : ℝ) :
    Set (Fin (n + 2) → ℝ) :=
  {g | (∑ j ∈ Finset.range (n + 1), padWaitPrefix n g j) ≤ t ∧
    t < ∑ j ∈ Finset.range (n + 2), padWaitPrefix n g j}

end AvramChat06


