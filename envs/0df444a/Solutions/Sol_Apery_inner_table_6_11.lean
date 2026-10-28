-- Prove2me | solution 1 for Apery.inner_table_6_11
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:19:20.777306+00:00
-- url     : https://prove2.me/submissions/4750f3c3-64dc-48b3-b47e-dea4744cc4d9

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables
import Theorems.Thm_Apery_inner_table_6_8
import Theorems.Thm_Apery_inner_table_9_11

open Finset

open Apery in
theorem solution : ∀ i, 6 ≤ i → i < 12 → ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)), Ein x (kIn i) = gIn i x := by
  intro i h1 h2
  by_cases c0 : i < 9
  · exact Apery.inner_table_6_8 i (by omega) c0
  exact Apery.inner_table_9_11 i (by omega) (by omega)
