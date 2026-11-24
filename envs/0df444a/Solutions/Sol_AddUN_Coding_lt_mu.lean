-- Prove2me | solution 1 for AddUN.Coding.lt_mu
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:23:51.312544+00:00
-- url     : https://prove2.me/submissions/f15a906a-8e7a-4c3c-9249-81526803c46e

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
theorem _root_.solution (n : ℕ) : n < mu n :=
  (Nat.lt_pow_self (by norm_num)).trans (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self n))
end AddUN.Coding
