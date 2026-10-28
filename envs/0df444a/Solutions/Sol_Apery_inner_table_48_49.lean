-- Prove2me | solution 1 for Apery.inner_table_48_49
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:19:40.730985+00:00
-- url     : https://prove2.me/submissions/3ad07021-50aa-4105-a952-6c45d7286a9b

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables
import Theorems.Thm_Apery_inner_table_48_48
import Theorems.Thm_Apery_inner_table_49_49

open Finset

open Apery in
theorem solution : ∀ i, 48 ≤ i → i < 50 → ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)), Ein x (kIn i) = gIn i x := by
  intro i h1 h2
  by_cases c0 : i < 49
  · exact Apery.inner_table_48_48 i (by omega) c0
  exact Apery.inner_table_49_49 i (by omega) (by omega)
