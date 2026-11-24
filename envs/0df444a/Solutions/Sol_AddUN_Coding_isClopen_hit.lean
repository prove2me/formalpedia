-- Prove2me | solution 1 for AddUN.Coding.isClopen_hit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:38:23.655631+00:00
-- url     : https://prove2.me/submissions/f22650dc-b948-4195-84e8-ded91486c9e4

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
theorem _root_.solution (c : ℕ → Bool) (n k : ℕ) : IsClopen (hit c n k) := isClopen_cylinderOn _ _
end AddUN.Coding
