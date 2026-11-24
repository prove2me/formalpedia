-- Prove2me | solution 1 for AddUN.Coding.low_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:37:10.299526+00:00
-- url     : https://prove2.me/submissions/3b12d7f1-eb92-477c-bbe7-61373976bf6f

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
theorem _root_.solution {m n : ℕ} (h : m ≤ n) : low m ⊆ low n := fun _ hi ↦ lt_of_lt_of_le hi h
end AddUN.Coding
