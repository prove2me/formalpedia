-- Prove2me | Definitions.Def_AvramChat06_MaskedWaitPrefixCylinder
-- name    : AvramChat06_MaskedWaitPrefixCylinder
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-20T15:59:50.676993+00:00
-- url     : https://prove2.me/theorems/d3169a08-5f50-4cba-a148-8edba906bebb
-- title:
--   Masked infinite waiting prefix and positive count observation cylinder
-- statement:
--   Reusable pinned Lean declarations underlying the Chat 06 verified Poisson waiting-time and finite observation cylinders. Imported by subsequent theorem proof targets without locally redeclaring definitions in their preambles.
-- source:
--   Chat 06 verified local definitions extracted verbatim from bv_positive_count_event_masked_past_cylinder_chat06_20261020.lean.

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Topology.Order.Basic

open MeasureTheory Set

namespace AvramChat06

def maskedWaitPrefix {Ω : Type*}
    (τ : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) (i : ℕ) : ℝ :=
  if i < k then τ i ω else 0

/-- Cylinder for the event that observation time t is between
the (n+1)-st and (n+2)-nd arrival times. -/
def positiveCountPastCylinder (n : ℕ) (t : ℝ) :
    Set (ℕ → ℝ) :=
  {g | (∑ i ∈ Finset.range (n + 1), g i) ≤ t ∧
    t < ∑ i ∈ Finset.range (n + 2), g i}

end AvramChat06


