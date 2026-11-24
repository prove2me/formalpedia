-- Prove2me | solution 1 for AddUN.Coding.hit_subset_marker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:38:49.237083+00:00
-- url     : https://prove2.me/submissions/d2eee42f-a8be-45e7-ae03-2876f8fd1e02

module
public import Definitions.Def_AddUN_SecondMoment
public import Definitions.Def_AddUN_TheoremB
public import Definitions.Def_AddUN_Coding
public import Theorems.Thm_AddUN_Coding_pattern_coord_of_lt
public import Theorems.Thm_AddUN_Coding_mem_marker
public import Theorems.Thm_AddUN_Coding_mem_hit

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory
open AddUN
open AddUN.Coding
namespace AddUN.Coding
theorem _root_.solution (c : ℕ → Bool) (n k : ℕ) : hit c n k ⊆ marker n k := by
  intro w hw
  rw [mem_marker]
  intro j hj
  rw [mem_hit.1 hw j (by omega), pattern_coord_of_lt c k hj]
end AddUN.Coding
