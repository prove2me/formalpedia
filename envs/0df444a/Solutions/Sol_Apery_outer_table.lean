-- Prove2me | solution 1 for Apery.outer_table
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T16:22:16.409168+00:00
-- url     : https://prove2.me/submissions/f7cbb175-a617-4bcf-8df9-7d04cf36e640

/-
# Irrationality of $\zeta(5)$ via normalized Hankel determinants
# The outer table (source `Apery/Growth/OuterTable.lean`)

This file proves the platform theorem `Apery.outer_table`: on each piece of the grid
$20/37, 40/43, 1, 40/37, 3/2, 20/13, 60/37, 80/43, 2, 80/37, 5/2, 100/37, 120/43, 3$ the
continuous outer profile $E_{\mathrm{out}}$ agrees with the affine table $g_{\mathrm{out}}$.
The proof assembles the two halves `Apery.outer_table_lo` (pieces 0-6) and
`Apery.outer_table_hi` (pieces 7-12) of the generated table of the pinned source project
mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0,
`Apery/Growth/OuterTable.lean`.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables
import Theorems.Thm_Apery_outer_table_lo
import Theorems.Thm_Apery_outer_table_hi

set_option autoImplicit false

section Port0
/-!
# The outer table (assembled from its two halves)

This file proves the platform theorem `Apery.outer_table` from the two halves
`Apery.outer_table_lo` (pieces 0-6) and `Apery.outer_table_hi` (pieces 7-12) of the generated
table of mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0,
`Apery/Growth/OuterTable.lean`.
-/

set_option autoImplicit false

open Finset

namespace Apery

theorem outer_table : ∀ i < 13, ∀ x ∈ Set.Ico (tOut i) (tOut (i + 1)), Eout x = gOut i x := by
  intro i hi x hx
  rcases lt_or_ge i 7 with h | h
  · exact outer_table_lo i h x hx
  · exact outer_table_hi i h hi x hx

end Apery

#check @Apery.outer_table
end Port0


open Finset in
/-- The platform target `Apery.outer_table`, restated at top level as `solution`. -/
theorem solution : ∀ i < 13, ∀ x ∈ Set.Ico (Apery.tOut i) (Apery.tOut (i + 1)),
    Apery.Eout x = Apery.gOut i x :=
  Apery.outer_table
