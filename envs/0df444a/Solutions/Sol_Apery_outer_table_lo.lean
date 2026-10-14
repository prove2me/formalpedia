-- Prove2me | solution 1 for Apery.outer_table_lo
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T17:43:32.641169+00:00
-- url     : https://prove2.me/submissions/18b8bea7-a568-4cfe-8d06-a3ab2457ad02

/-
# Irrationality of $\zeta(5)$ via normalized Hankel determinants
# The first seven pieces of the outer table, assembled from two blocks

This file proves the platform theorem `Apery.outer_table_lo` (pieces 0-6 of
`Apery/Growth/OuterTable.lean`) from the two size-split blocks `Apery.outer_table_0_3` and
`Apery.outer_table_4_6`. Port of mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables
import Theorems.Thm_Apery_outer_table_0_3
import Theorems.Thm_Apery_outer_table_4_6

set_option autoImplicit false

section Port0
/-!
# The first seven pieces of the outer table, assembled from two blocks.
-/

set_option autoImplicit false

open Finset

namespace Apery

theorem outer_table_lo : ∀ i < 7, ∀ x ∈ Set.Ico (tOut i) (tOut (i + 1)), Eout x = gOut i x := by
  intro i hi x hx
  rcases lt_or_ge i 4 with h | h
  · exact outer_table_0_3 i (Nat.zero_le i) h x hx
  · exact outer_table_4_6 i h hi x hx

end Apery
end Port0


open Finset in
/-- The platform target `Apery.outer_table_lo`, restated at top level as `solution`. -/
theorem solution : ∀ i < 7, ∀ x ∈ Set.Ico (Apery.tOut i) (Apery.tOut (i + 1)),
    Apery.Eout x = Apery.gOut i x :=
  Apery.outer_table_lo
