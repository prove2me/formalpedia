-- Prove2me | solution 1 for AddUN.Coding.card_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:37:14.367949+00:00
-- url     : https://prove2.me/submissions/bfb2da3b-e9e7-4ee9-b20f-cb0e55bf04b8

module
public import Definitions.Def_AddUN_SecondMoment
public import Definitions.Def_AddUN_TheoremB
public import Definitions.Def_AddUN_Coding
public import Theorems.Thm_AddUN_Coding_coord_inj

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory
open AddUN
open AddUN.Coding
namespace AddUN.Coding
theorem _root_.solution (n k : ℕ) : (block n k).card = mu n + n := by
  rw [block, Finset.card_image_of_injective _ fun a b h ↦ (coord_inj.1 h).2.2, Finset.card_range]
end AddUN.Coding
