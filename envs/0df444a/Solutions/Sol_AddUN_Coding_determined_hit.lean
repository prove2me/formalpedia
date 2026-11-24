-- Prove2me | solution 1 for AddUN.Coding.determined_hit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:38:40.426444+00:00
-- url     : https://prove2.me/submissions/e6238537-e929-4647-8b14-11c46809dfce

module
public import Definitions.Def_AddUN_SecondMoment
public import Definitions.Def_AddUN_TheoremB
public import Definitions.Def_AddUN_Coding
public import Theorems.Thm_AddUN_Coding_block_subset_low
public import Theorems.Thm_MeasureTheory_determined_cylinderOn


set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory
open AddUN
open AddUN.Coding
namespace AddUN.Coding
theorem _root_.solution (c : ℕ → Bool) (n k : ℕ) : Determined (low (n + 1)) (hit c n k) :=
  determined_cylinderOn _ _ (block_subset_low n k)
end AddUN.Coding
