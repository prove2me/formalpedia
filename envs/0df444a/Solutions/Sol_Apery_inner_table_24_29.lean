-- Prove2me | solution 1 for Apery.inner_table_24_29
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:19:30.486527+00:00
-- url     : https://prove2.me/submissions/5d6be051-884c-467a-84b2-711683dacb51

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables
import Theorems.Thm_Apery_inner_table_24_26
import Theorems.Thm_Apery_inner_table_27_29

open Finset

open Apery in
theorem solution : ∀ i, 24 ≤ i → i < 30 → ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)), Ein x (kIn i) = gIn i x := by
  intro i h1 h2
  by_cases c0 : i < 27
  · exact Apery.inner_table_24_26 i (by omega) c0
  exact Apery.inner_table_27_29 i (by omega) (by omega)
