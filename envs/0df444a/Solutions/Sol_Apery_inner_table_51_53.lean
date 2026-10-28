-- Prove2me | solution 1 for Apery.inner_table_51_53
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:20:11.597544+00:00
-- url     : https://prove2.me/submissions/2a959623-cfa0-4354-bd2f-77bd615ef3bb

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables
import Theorems.Thm_Apery_inner_table_51_52
import Theorems.Thm_Apery_inner_table_53_53

open Finset

open Apery in
theorem solution : ∀ i, 51 ≤ i → i < 54 → ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)), Ein x (kIn i) = gIn i x := by
  intro i h1 h2
  by_cases c0 : i < 53
  · exact Apery.inner_table_51_52 i (by omega) c0
  exact Apery.inner_table_53_53 i (by omega) (by omega)
