-- Prove2me | solution 1 for Apery.inner_table
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T23:21:03.588287+00:00
-- url     : https://prove2.me/submissions/39b3690c-e75e-4a81-ad27-03d5010ca915

/-
# The inner table (source `Apery/Growth/InnerSum.lean`)

This file proves `Apery.inner_table` (the 125-piece inner table) by assembling the
size-split blocks `Apery.inner_table_a_b` with the index case split. Faithful to
mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, `Apery/Growth/InnerSum.lean`.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables
import Theorems.Thm_Apery_inner_table_0_5
import Theorems.Thm_Apery_inner_table_6_8
import Theorems.Thm_Apery_inner_table_9_11
import Theorems.Thm_Apery_inner_table_12_17
import Theorems.Thm_Apery_inner_table_18_23
import Theorems.Thm_Apery_inner_table_24_26
import Theorems.Thm_Apery_inner_table_27_29
import Theorems.Thm_Apery_inner_table_30_35
import Theorems.Thm_Apery_inner_table_36_41
import Theorems.Thm_Apery_inner_table_42_47
import Theorems.Thm_Apery_inner_table_48_48
import Theorems.Thm_Apery_inner_table_49_49
import Theorems.Thm_Apery_inner_table_50_50
import Theorems.Thm_Apery_inner_table_51_52
import Theorems.Thm_Apery_inner_table_53_53
import Theorems.Thm_Apery_inner_table_54_55
import Theorems.Thm_Apery_inner_table_56_56
import Theorems.Thm_Apery_inner_table_57_58
import Theorems.Thm_Apery_inner_table_59_59
import Theorems.Thm_Apery_inner_table_60_65
import Theorems.Thm_Apery_inner_table_66_71
import Theorems.Thm_Apery_inner_table_72_77
import Theorems.Thm_Apery_inner_table_78_80
import Theorems.Thm_Apery_inner_table_81_83
import Theorems.Thm_Apery_inner_table_84_89
import Theorems.Thm_Apery_inner_table_90_92
import Theorems.Thm_Apery_inner_table_93_95
import Theorems.Thm_Apery_inner_table_96_101
import Theorems.Thm_Apery_inner_table_102_104
import Theorems.Thm_Apery_inner_table_105_106
import Theorems.Thm_Apery_inner_table_107_107
import Theorems.Thm_Apery_inner_table_108_113
import Theorems.Thm_Apery_inner_table_114_119
import Theorems.Thm_Apery_inner_table_120_124

set_option autoImplicit false

section Port0

open Finset

namespace Apery

theorem inner_table_asm : ∀ i < 125, ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)), Ein x (kIn i) = gIn i x := by
  intro i hi x hx
  rcases lt_or_ge i 6 with h0 | h0
  · exact inner_table_0_5 i (by omega) (by omega) x hx
  rcases lt_or_ge i 9 with h1 | h1
  · exact inner_table_6_8 i (by omega) (by omega) x hx
  rcases lt_or_ge i 12 with h2 | h2
  · exact inner_table_9_11 i (by omega) (by omega) x hx
  rcases lt_or_ge i 18 with h3 | h3
  · exact inner_table_12_17 i (by omega) (by omega) x hx
  rcases lt_or_ge i 24 with h4 | h4
  · exact inner_table_18_23 i (by omega) (by omega) x hx
  rcases lt_or_ge i 27 with h5 | h5
  · exact inner_table_24_26 i (by omega) (by omega) x hx
  rcases lt_or_ge i 30 with h6 | h6
  · exact inner_table_27_29 i (by omega) (by omega) x hx
  rcases lt_or_ge i 36 with h7 | h7
  · exact inner_table_30_35 i (by omega) (by omega) x hx
  rcases lt_or_ge i 42 with h8 | h8
  · exact inner_table_36_41 i (by omega) (by omega) x hx
  rcases lt_or_ge i 48 with h9 | h9
  · exact inner_table_42_47 i (by omega) (by omega) x hx
  rcases lt_or_ge i 49 with h10 | h10
  · exact inner_table_48_48 i (by omega) (by omega) x hx
  rcases lt_or_ge i 50 with h11 | h11
  · exact inner_table_49_49 i (by omega) (by omega) x hx
  rcases lt_or_ge i 51 with h12 | h12
  · exact inner_table_50_50 i (by omega) (by omega) x hx
  rcases lt_or_ge i 53 with h13 | h13
  · exact inner_table_51_52 i (by omega) (by omega) x hx
  rcases lt_or_ge i 54 with h14 | h14
  · exact inner_table_53_53 i (by omega) (by omega) x hx
  rcases lt_or_ge i 56 with h15 | h15
  · exact inner_table_54_55 i (by omega) (by omega) x hx
  rcases lt_or_ge i 57 with h16 | h16
  · exact inner_table_56_56 i (by omega) (by omega) x hx
  rcases lt_or_ge i 59 with h17 | h17
  · exact inner_table_57_58 i (by omega) (by omega) x hx
  rcases lt_or_ge i 60 with h18 | h18
  · exact inner_table_59_59 i (by omega) (by omega) x hx
  rcases lt_or_ge i 66 with h19 | h19
  · exact inner_table_60_65 i (by omega) (by omega) x hx
  rcases lt_or_ge i 72 with h20 | h20
  · exact inner_table_66_71 i (by omega) (by omega) x hx
  rcases lt_or_ge i 78 with h21 | h21
  · exact inner_table_72_77 i (by omega) (by omega) x hx
  rcases lt_or_ge i 81 with h22 | h22
  · exact inner_table_78_80 i (by omega) (by omega) x hx
  rcases lt_or_ge i 84 with h23 | h23
  · exact inner_table_81_83 i (by omega) (by omega) x hx
  rcases lt_or_ge i 90 with h24 | h24
  · exact inner_table_84_89 i (by omega) (by omega) x hx
  rcases lt_or_ge i 93 with h25 | h25
  · exact inner_table_90_92 i (by omega) (by omega) x hx
  rcases lt_or_ge i 96 with h26 | h26
  · exact inner_table_93_95 i (by omega) (by omega) x hx
  rcases lt_or_ge i 102 with h27 | h27
  · exact inner_table_96_101 i (by omega) (by omega) x hx
  rcases lt_or_ge i 105 with h28 | h28
  · exact inner_table_102_104 i (by omega) (by omega) x hx
  rcases lt_or_ge i 107 with h29 | h29
  · exact inner_table_105_106 i (by omega) (by omega) x hx
  rcases lt_or_ge i 108 with h30 | h30
  · exact inner_table_107_107 i (by omega) (by omega) x hx
  rcases lt_or_ge i 114 with h31 | h31
  · exact inner_table_108_113 i (by omega) (by omega) x hx
  rcases lt_or_ge i 120 with h32 | h32
  · exact inner_table_114_119 i (by omega) (by omega) x hx
  · exact inner_table_120_124 i (by omega) (by omega) x hx

end Apery

end Port0

open Finset in
/-- The platform target `Apery.inner_table`, restated at top level as `solution`. -/
theorem solution : ∀ i < 125, ∀ x ∈ Set.Ico (Apery.tIn i) (Apery.tIn (i + 1)),
    Apery.Ein x (Apery.kIn i) = Apery.gIn i x :=
  Apery.inner_table_asm
