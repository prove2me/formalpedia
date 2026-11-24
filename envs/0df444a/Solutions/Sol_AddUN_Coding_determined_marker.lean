-- Prove2me | solution 1 for AddUN.Coding.determined_marker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:38:28.617825+00:00
-- url     : https://prove2.me/submissions/fda1e703-0e99-40cc-b46f-6a58405d60d3

module
public import Definitions.Def_AddUN_SecondMoment
public import Definitions.Def_AddUN_TheoremB
public import Definitions.Def_AddUN_Coding
public import Theorems.Thm_AddUN_Coding_block_subset_low
public import Theorems.Thm_AddUN_Coding_markerBlock_subset_block
public import Theorems.Thm_MeasureTheory_determined_cylinderOn


set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory
open AddUN
open AddUN.Coding
namespace AddUN.Coding
theorem _root_.solution (n k : ℕ) : Determined (low (n + 1)) (marker n k) :=
  determined_cylinderOn _ _
    ((Finset.coe_subset.2 (markerBlock_subset_block n k)).trans (block_subset_low n k))
end AddUN.Coding
