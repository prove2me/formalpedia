-- Prove2me | solution 1 for AddUN.codingLemma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:43:16.76081+00:00
-- url     : https://prove2.me/submissions/60332a7b-6a67-4a6c-8f32-c66fe592e23c

module
public import Definitions.Def_AddUN_SecondMoment
public import Definitions.Def_AddUN_TheoremB
public import Definitions.Def_AddUN_Coding
public import Theorems.Thm_AddUN_Coding_measurable_decode
public import Theorems.Thm_AddUN_exists_slalom_decode

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory
open AddUN
open Coding
namespace AddUN
theorem _root_.solution : CodingLemma :=
  ⟨fun n ↦ 2 ^ (3 * mu n + n), decode, measurable_decode, fun _ hK hKpos c ↦
    exists_slalom_decode hK hKpos c⟩
end AddUN
