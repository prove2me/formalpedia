-- Prove2me | solution 1 for Apery.inner_table_102_107
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:21:14.379998+00:00
-- url     : https://prove2.me/submissions/a3635ec7-e070-482e-b3b7-a16916efaf4c

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables
import Theorems.Thm_Apery_inner_table_102_104
import Theorems.Thm_Apery_inner_table_105_106
import Theorems.Thm_Apery_inner_table_107_107

open Finset

open Apery in
theorem solution : ∀ i, 102 ≤ i → i < 108 → ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)), Ein x (kIn i) = gIn i x := by
  intro i h1 h2
  by_cases c0 : i < 105
  · exact Apery.inner_table_102_104 i (by omega) c0
  by_cases c1 : i < 107
  · exact Apery.inner_table_105_106 i (by omega) c1
  exact Apery.inner_table_107_107 i (by omega) (by omega)
