-- Prove2me | solution 1 for AddUN.Coding.card_markerBlock
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:30:07.289067+00:00
-- url     : https://prove2.me/submissions/3d204208-9099-4959-8df7-c43b259781b9

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
theorem _root_.solution (n k : ℕ) : (markerBlock n k).card = mu n := by
  rw [markerBlock, Finset.card_image_of_injective _ fun a b h ↦ (coord_inj.1 h).2.2,
    Finset.card_range]
end AddUN.Coding
