-- Prove2me | solution 1 for Apery.inner_table_78_83
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:20:53.642868+00:00
-- url     : https://prove2.me/submissions/d8353f55-7fa1-480c-a248-e58b1db00fb4

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables
import Theorems.Thm_Apery_inner_table_78_80
import Theorems.Thm_Apery_inner_table_81_83

open Finset

open Apery in
theorem solution : ∀ i, 78 ≤ i → i < 84 → ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)), Ein x (kIn i) = gIn i x := by
  intro i h1 h2
  by_cases c0 : i < 81
  · exact Apery.inner_table_78_80 i (by omega) c0
  exact Apery.inner_table_81_83 i (by omega) (by omega)
