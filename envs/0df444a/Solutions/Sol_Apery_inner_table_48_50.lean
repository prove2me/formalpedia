-- Prove2me | solution 1 for Apery.inner_table_48_50
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:19:51.34483+00:00
-- url     : https://prove2.me/submissions/4c80aaf0-1e58-4933-9999-6f985c41b9e1

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables
import Theorems.Thm_Apery_inner_table_48_48
import Theorems.Thm_Apery_inner_table_49_49
import Theorems.Thm_Apery_inner_table_50_50

open Finset

open Apery in
theorem solution : ∀ i, 48 ≤ i → i < 51 → ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)), Ein x (kIn i) = gIn i x := by
  intro i h1 h2
  by_cases c0 : i < 49
  · exact Apery.inner_table_48_48 i (by omega) c0
  by_cases c1 : i < 50
  · exact Apery.inner_table_49_49 i (by omega) c1
  exact Apery.inner_table_50_50 i (by omega) (by omega)
