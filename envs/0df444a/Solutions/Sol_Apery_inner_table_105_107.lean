-- Prove2me | solution 1 for Apery.inner_table_105_107
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:21:23.980579+00:00
-- url     : https://prove2.me/submissions/518b7892-3e03-4d4b-8d36-2f9916df14f2

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables
import Theorems.Thm_Apery_inner_table_105_106
import Theorems.Thm_Apery_inner_table_107_107

open Finset

open Apery in
theorem solution : ∀ i, 105 ≤ i → i < 108 → ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)), Ein x (kIn i) = gIn i x := by
  intro i h1 h2
  by_cases c0 : i < 107
  · exact Apery.inner_table_105_106 i (by omega) c0
  exact Apery.inner_table_107_107 i (by omega) (by omega)
