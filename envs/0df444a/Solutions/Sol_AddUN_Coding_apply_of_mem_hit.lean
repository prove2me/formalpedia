-- Prove2me | solution 1 for AddUN.Coding.apply_of_mem_hit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:38:45.257643+00:00
-- url     : https://prove2.me/submissions/caf6f994-a165-49b5-ab34-4cacb395f71c

module
public import Definitions.Def_AddUN_SecondMoment
public import Definitions.Def_AddUN_TheoremB
public import Definitions.Def_AddUN_Coding
public import Theorems.Thm_AddUN_Coding_pattern_coord_add
public import Theorems.Thm_AddUN_Coding_mem_hit

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory
open AddUN
open AddUN.Coding
namespace AddUN.Coding
theorem _root_.solution {c : ℕ → Bool} {n k i : ℕ} {w : ℕ → Bool} (hw : w ∈ hit c n k)
    (hi : i < n) : w (coord n k (mu n + i)) = c i := by
  rw [mem_hit.1 hw _ (by omega), pattern_coord_add]
end AddUN.Coding
