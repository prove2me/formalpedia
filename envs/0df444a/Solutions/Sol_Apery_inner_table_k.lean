-- Prove2me | solution 1 for Apery.inner_table_k
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T18:34:16.648002+00:00
-- url     : https://prove2.me/submissions/081d0262-5813-4d7a-b873-6e3a3944a5f5

/-
# The admissible k-window of the inner table (source `Apery/Growth/InnerSum.lean`)

This file proves `Apery.inner_table_k` by assembling its size-split blocks. Port of
mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables
import Theorems.Thm_Apery_inner_table_k_0_30
import Theorems.Thm_Apery_inner_table_k_31_61
import Theorems.Thm_Apery_inner_table_k_62_92
import Theorems.Thm_Apery_inner_table_k_93_124

set_option autoImplicit false

section Port0
set_option autoImplicit false

open Finset

namespace Apery

theorem inner_table_k : ∀ i < 125, ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)),
    -2 * (⌊x⌋₊ : ℤ) - 6 ≤ kIn i ∧ kIn i ≤ 8 * (⌊x⌋₊ : ℤ) + 20 := by
  intro i hi x hx
  rcases le_or_gt i 30 with h0 | h0
  · exact inner_table_k_0_30 i (Nat.zero_le i) h0 x hx
  rcases le_or_gt i 61 with h1 | h1
  · exact inner_table_k_31_61 i h0 h1 x hx
  rcases le_or_gt i 92 with h2 | h2
  · exact inner_table_k_62_92 i h1 h2 x hx
  · exact inner_table_k_93_124 i h2 (by omega) x hx

end Apery
end Port0


open Finset in
/-- The platform target `Apery.inner_table_k`, restated at top level as `solution`. -/
theorem solution : ∀ i < 125, ∀ x ∈ Set.Ico (Apery.tIn i) (Apery.tIn (i + 1)),
    -2 * (⌊x⌋₊ : ℤ) - 6 ≤ Apery.kIn i ∧ Apery.kIn i ≤ 8 * (⌊x⌋₊ : ℤ) + 20 :=
  Apery.inner_table_k
