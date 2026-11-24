-- Prove2me | solution 1 for AddUN.Coding.theta_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:30:48.884814+00:00
-- url     : https://prove2.me/submissions/ce041c83-0aca-4635-a161-da6cd71bcdfd

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
theorem _root_.solution (n : ℕ) : 0 < theta n := by
  unfold theta
  positivity
end AddUN.Coding
