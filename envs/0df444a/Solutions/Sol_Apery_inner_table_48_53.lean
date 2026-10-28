-- Prove2me | solution 1 for Apery.inner_table_48_53
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:20:01.592867+00:00
-- url     : https://prove2.me/submissions/15e75c4d-690c-40ff-a7b4-f2ec3ae85a71

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables
import Theorems.Thm_Apery_inner_table_48_48
import Theorems.Thm_Apery_inner_table_49_49
import Theorems.Thm_Apery_inner_table_50_50
import Theorems.Thm_Apery_inner_table_51_52
import Theorems.Thm_Apery_inner_table_53_53

open Finset

open Apery in
theorem solution : ∀ i, 48 ≤ i → i < 54 → ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)), Ein x (kIn i) = gIn i x := by
  intro i h1 h2
  by_cases c0 : i < 49
  · exact Apery.inner_table_48_48 i (by omega) c0
  by_cases c1 : i < 50
  · exact Apery.inner_table_49_49 i (by omega) c1
  by_cases c2 : i < 51
  · exact Apery.inner_table_50_50 i (by omega) c2
  by_cases c3 : i < 53
  · exact Apery.inner_table_51_52 i (by omega) c3
  exact Apery.inner_table_53_53 i (by omega) (by omega)
