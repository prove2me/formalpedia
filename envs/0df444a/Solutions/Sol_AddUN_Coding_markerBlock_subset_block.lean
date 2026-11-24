-- Prove2me | solution 1 for AddUN.Coding.markerBlock_subset_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:37:19.951698+00:00
-- url     : https://prove2.me/submissions/d2e7e6b6-85ca-4767-b84c-f0f17e305b59

module
public import Definitions.Def_AddUN_SecondMoment
public import Definitions.Def_AddUN_TheoremB
public import Definitions.Def_AddUN_Coding

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory
open AddUN
open AddUN.Coding
namespace AddUN.Coding
theorem _root_.solution (n k : ℕ) : markerBlock n k ⊆ block n k :=
  Finset.image_subset_image (Finset.range_subset_range.2 (Nat.le_add_right _ _))
end AddUN.Coding
