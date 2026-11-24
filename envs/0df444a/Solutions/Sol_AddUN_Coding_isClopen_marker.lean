-- Prove2me | solution 1 for AddUN.Coding.isClopen_marker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:37:22.523496+00:00
-- url     : https://prove2.me/submissions/ecca7701-7b31-40be-8417-b48dae35904b

module
public import Definitions.Def_AddUN_SecondMoment
public import Definitions.Def_AddUN_TheoremB
public import Definitions.Def_AddUN_Coding
public import Theorems.Thm_MeasureTheory_isClopen_cylinderOn


set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory
open AddUN
open AddUN.Coding
namespace AddUN.Coding
theorem _root_.solution (n k : ℕ) : IsClopen (marker n k) := isClopen_cylinderOn _ _
end AddUN.Coding
