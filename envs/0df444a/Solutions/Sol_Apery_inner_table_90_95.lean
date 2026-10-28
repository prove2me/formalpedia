-- Prove2me | solution 1 for Apery.inner_table_90_95
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:21:02.890769+00:00
-- url     : https://prove2.me/submissions/c0841dc2-80c6-445c-869f-520c54870c7b

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables
import Theorems.Thm_Apery_inner_table_90_92
import Theorems.Thm_Apery_inner_table_93_95

open Finset

open Apery in
theorem solution : ∀ i, 90 ≤ i → i < 96 → ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)), Ein x (kIn i) = gIn i x := by
  intro i h1 h2
  by_cases c0 : i < 93
  · exact Apery.inner_table_90_92 i (by omega) c0
  exact Apery.inner_table_93_95 i (by omega) (by omega)
