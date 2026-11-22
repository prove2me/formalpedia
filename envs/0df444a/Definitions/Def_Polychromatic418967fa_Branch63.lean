-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch63
-- name    : Polychromatic418967fa_Branch63
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:08:40.854278+00:00
-- url     : https://prove2.me/theorems/954c7fe0-094d-40a7-8c64-a8bc4252f96b
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_63 : allB 63 63 :=
  allB_succ' 2 62 63 (Eq.refl Bool.true) (allA_succ_of_accept 1 62 63 (accept_3_4 1 62 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 62 63)) (allB_succ' 3 61 63 (Eq.refl Bool.true) (allA_succ_of_accept 2 61 63 (accept_3_5 2 61 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 63 (Polychromatic418967fa.accept_13_1_9_11_1_703 1
  61 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 63))) (allB_succ' 4 60 63 (Eq.refl
  Bool.true) (allA_succ_of_gcd 3 60 63 3 1 20 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 2 60 63 (Polychromatic418967fa.accept_11_2_5_8_1_470 2 60 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 63 (Polychromatic418967fa.accept_13_1_8_11_1_724 1
  60 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60 63)))) (allB_succ' 5 59 63 (Eq.refl
  Bool.true) (allA_succ_of_accept 4 59 63 (accept_3_4 4 59 63 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 59 63 (Polychromatic418967fa.accept_13_3_7_11_1_1904 3 59 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 63 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 59 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 63 (accept_3_4 1 59 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 59 63))))) (allB_succ' 6 58 63 (Eq.refl Bool.true) (allA_succ_of_accept 5 58
  63 (accept_3_5 5 58 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58 63
  (Polychromatic418967fa.accept_13_4_6_11_1_2017 4 58 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 58 63 (Polychromatic418967fa.accept_17_3_7_12_1_2016 3 58 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 63 (accept_3_5 2 58 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 58 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 58 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58 63)))))) (allB_succ' 7 57 63 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 57 63 3 2 19 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 57 63 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 57 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 63 (Polychromatic418967fa.accept_10_4_7_3_1_54 4 57 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 63 3 1 19 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 63
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 57 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 63 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 57 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 57 63))))))) (allB_succ' 8 56 63 (Eq.refl Bool.true) (allA_succ_of_gcd 7 56
  63 7 1 8 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 56
  63 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 56 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 63 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 56 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 63 (accept_3_4 4 56 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 63 (Polychromatic418967fa.accept_18_3_2_9_1_1013 3 56 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 63 (Polychromatic418967fa.accept_13_2_4_11_1_2003 2
  56 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 63 (accept_3_4 1 56 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 63)))))))) (allB_succ' 9 55 63 (Eq.refl Bool.true)
  (allA_succ_of_accept 8 55 63 (accept_3_5 8 55 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 63
  (Polychromatic418967fa.accept_10_7_5_3_1_542 7 55 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 55 63 (Polychromatic418967fa.accept_14_6_13_7_1_2015 6 55 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 63 (accept_3_5 5 55 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 55 63 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 55 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 63 (Polychromatic418967fa.accept_16_3_7_15_1_1130 3
  55 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 63 (accept_3_5 2 55 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 63 (Polychromatic418967fa.accept_13_1_3_11_1_1289 1
  55 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 63))))))))) (allB_succ' 10 54 63
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 54 63 9 1 6 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 8 54 63 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 54 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 63
  (Polychromatic418967fa.accept_10_7_4_3_1_560 7 54 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 54 63 3 2 18 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 54 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 54 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 63 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 54 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 54 63 3 1 18 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 54 63
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 54 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 54 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 54 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 54 63)))))))))) (allB_succ' 11 53 63 (Eq.refl Bool.true) (allA_succ_of_accept 10 53 63
  (accept_3_4 10 53 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 63
  (Polychromatic418967fa.accept_12_9_5_3_1_782 9 53 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 53 63 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 53 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 63 (accept_3_4 7 53 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 53 63 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 53 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 63 (Polychromatic418967fa.accept_15_5_8_3_1_556 5
  53 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 63 (accept_3_4 4 53 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53 63 (Polychromatic418967fa.accept_13_3_1_11_1_1268 3
  53 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 63
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 53 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 53 63 (accept_3_4 1 53 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53 63)))))))))))
  (allB_succ' 12 52 63 (Eq.refl Bool.true) (allA_succ_of_accept 11 52 63 (accept_3_5 11 52 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 52 63 (Polychromatic418967fa.accept_15_10_7_3_1_1939 10 52 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 52 63
  (Polychromatic418967fa.accept_19_9_14_6_1_2014 9 52 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 52 63 (accept_3_5 8 52 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 63
  (Polychromatic418967fa.accept_6_1_4_3_1_14 7 52 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 52 63 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 52 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 52 63 (accept_3_5 5 52 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 52 63 (Polychromatic418967fa.accept_14_4_10_7_1_1946 4 52 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 52 63 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 52
  63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 63 (accept_3_5 2 52 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 52 63 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 52
  63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 63)))))))))))) (allB_succ' 13 51 63
  (Eq.refl Bool.true) (allA_succ_of_gcd 12 51 63 3 4 17 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 51 63 (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 51 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 63
  (Polychromatic418967fa.accept_13_10_12_11_1_731 10 51 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 51 63 3 3 17 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 51 63 (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 51 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 63 (Polychromatic418967fa.accept_13_7_12_11_1_1911 7 51 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 63 3 2 17 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 63
  (Polychromatic418967fa.accept_14_5_9_7_1_590 5 51 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 63 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 51 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 63 3 1 17 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 63 (Polychromatic418967fa.accept_10_2_1_3_1_233 2 51 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 63
  (Polychromatic418967fa.accept_13_1_12_11_1_728 1 51 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 51 63))))))))))))) (allB_succ' 14 50 63 (Eq.refl Bool.true) (allA_succ_of_accept 13 50 63 (accept_3_4 13 50
  63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 50 63
  (Polychromatic418967fa.accept_16_12_2_15_1_490 12 50 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 50 63 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 50 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 63 (accept_3_4 10 50 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 50 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 50 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 63 (Polychromatic418967fa.accept_15_8_5_3_1_1990 8
  50 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 50 63 (accept_3_4 7 50 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50 63 (Polychromatic418967fa.accept_12_6_2_3_1_354 6
  50 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 50 63
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 50 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 50 63 (accept_3_4 4 50 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 50 63
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 50 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 50 63 (Polychromatic418967fa.accept_15_2_5_3_1_552 2 50 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 63 (accept_3_4 1 50 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 50 63)))))))))))))) (allB_succ' 15 49 63 (Eq.refl Bool.true) (allA_succ_of_gcd 14 49 63 7 2 7 9
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 49 63
  (Polychromatic418967fa.accept_11_2_5_8_1_470 13 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 49 63 (Polychromatic418967fa.accept_13_12_10_11_1_1279 12 49 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 63 (accept_3_5 11 49 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 49 63 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 49 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 63 (Polychromatic418967fa.accept_12_9_1_3_1_350 9
  49 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 63 (accept_3_5 8 49 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 49 63 7 1 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 49 63 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 49
  63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 63 (accept_3_5 5 49 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49 63 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 49
  63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 63
  (Polychromatic418967fa.accept_11_3_5_8_1_458 3 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 49 63 (accept_3_5 2 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 63
  (Polychromatic418967fa.accept_13_1_10_11_1_1280 1 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 49 63))))))))))))))) (allB_succ' 16 48 63 (Eq.refl Bool.true) (allA_succ_of_gcd 15 48 63 3 5 16 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 48 63
  (Polychromatic418967fa.accept_13_1_9_11_1_703 14 48 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 48 63 (Polychromatic418967fa.accept_14_13_6_7_1_2013 13 48 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 63 3 4 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 63 (Polychromatic418967fa.accept_10_1_8_3_1_947 11 48 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 63
  (Polychromatic418967fa.accept_18_10_12_9_1_2012 10 48 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 48 63 3 3 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 48 63 (Polychromatic418967fa.accept_13_8_9_11_1_1265 8 48 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 63 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 48 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 63 3 2 16 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 63
  (Polychromatic418967fa.accept_10_5_8_3_1_229 5 48 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 63 (Polychromatic418967fa.accept_18_4_12_9_1_2011 4 48 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 48 63 3 1 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 48 63 (Polychromatic418967fa.accept_13_2_9_11_1_258 2 48 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 63
  (Polychromatic418967fa.accept_10_1_8_3_1_947 1 48 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 48 63)))))))))))))))) (allB_succ' 17 47 63 (Eq.refl Bool.true) (allA_succ_of_accept 16 47 63 (accept_3_4 16
  47 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 63
  (Polychromatic418967fa.accept_10_5_7_3_1_561 15 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 47 63 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 47 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 63 (accept_3_4 13 47 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 47 63 (Polychromatic418967fa.accept_14_12_5_7_1_2010 12 47 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 63
  (Polychromatic418967fa.accept_17_11_13_12_1_1968 11 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 63 (accept_3_4 10 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 47
  63 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 47 63 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 47 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 63 (accept_3_4 7 47 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 47 63 (Polychromatic418967fa.accept_10_6_7_3_1_547 6 47 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 63 (Polychromatic418967fa.accept_10_5_7_3_1_561 5
  47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 63 (accept_3_4 4 47 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 63 (Polychromatic418967fa.accept_13_3_8_11_1_1906 3
  47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 63
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 47 63 (accept_3_4 1 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47
  63))))))))))))))))) (allB_succ' 18 46 63 (Eq.refl Bool.true) (allA_succ_of_accept 17 46 63 (accept_3_5 17 46 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 63 (Polychromatic418967fa.accept_11_5_2_8_1_866 16
  46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 63
  (Polychromatic418967fa.accept_18_15_10_9_1_2009 15 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 63 (accept_3_5 14 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 46
  63 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 46 63 (Polychromatic418967fa.accept_13_12_7_11_1_1935 12 46 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 63 (accept_3_5 11 46 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 46 63 (Polychromatic418967fa.accept_14_10_4_7_1_1214 10 46 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 46
  63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 46 63 (accept_3_5 8 46 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46 63 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 46
  63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 46 63
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 46 63 (accept_3_5 5 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 46 63
  (Polychromatic418967fa.accept_13_4_7_11_1_1981 4 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 46 63 (Polychromatic418967fa.accept_13_3_7_11_1_1904 3 46 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 63 (accept_3_5 2 46 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 46 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 46 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46 63)))))))))))))))))) (allB_succ' 19 45 63 (Eq.refl Bool.true)
  (allA_succ_of_gcd 18 45 63 9 2 5 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 45 63 (Polychromatic418967fa.accept_10_7_5_3_1_542 17 45 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 63 (Polychromatic418967fa.accept_17_16_11_12_1_2008 16 45
  63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 63 3 5 15 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 63
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 45 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 63 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 45 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 45 63 3 4 15 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 45 63 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 45 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 63
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 45 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 45 63 9 1 5 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 45 63 (Polychromatic418967fa.accept_10_8_5_3_1_543 8 45 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 63 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 45 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 63 3 2 15 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 63
  (Polychromatic418967fa.accept_12_5_9_3_1_85 5 45 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 45 63 (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 45 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 45 63 3 1 15 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 45 63 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 45 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 63
  (Polychromatic418967fa.accept_12_1_9_3_1_370 1 45 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 45 63))))))))))))))))))) (allB_succ' 20 44 63 (Eq.refl Bool.true) (allA_succ_of_accept 19 44 63 (accept_3_4
  19 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 44 63
  (Polychromatic418967fa.accept_12_6_8_3_1_82 18 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 44 63 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 44 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 63 (accept_3_4 16 44 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 44 63 (Polychromatic418967fa.accept_23_15_21_17_1_2007 15 44 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 63
  (Polychromatic418967fa.accept_20_14_4_3_1_2006 14 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 63 (accept_3_4 13 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 44
  63 (Polychromatic418967fa.accept_14_12_2_7_1_1243 12 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 63 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 44 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 63 (accept_3_4 10 44 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 63 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 44 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 63
  (Polychromatic418967fa.accept_16_8_12_15_1_2005 8 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 63 (accept_3_4 7 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44 63
  (Polychromatic418967fa.accept_12_6_8_3_1_82 6 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 63 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 44 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 63 (accept_3_4 4 44 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 63 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 44 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 63 (Polychromatic418967fa.accept_15_2_14_3_1_1916 2
  44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 63 (accept_3_4 1 44 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 63)))))))))))))))))))) (allB_succ' 21 43 63 (Eq.refl Bool.true)
  (allA_succ_of_accept 20 43 63 (accept_3_5 20 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 43
  63 (Polychromatic418967fa.accept_13_6_4_11_1_282 19 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 43 63 (Polychromatic418967fa.accept_19_18_5_6_1_2004 18 43 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 63 (accept_3_5 17 43 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 43 63 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 43 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 63 (Polychromatic418967fa.accept_13_2_4_11_1_2003
  15 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 63 (accept_3_5 14 43
  63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 63
  (Polychromatic418967fa.accept_14_13_1_7_1_1211 13 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 43 63 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 43 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 63 (accept_3_5 11 43 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 43 63 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 43 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 63 (Polychromatic418967fa.accept_11_9_10_8_1_444 9
  43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 63 (accept_3_5 8 43 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 63 (Polychromatic418967fa.accept_13_7_4_11_1_1967 7
  43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 63
  (Polychromatic418967fa.accept_13_6_4_11_1_282 6 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 63 (accept_3_5 5 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43 63
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 63 (Polychromatic418967fa.accept_16_3_11_15_1_1963 3 43 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 63 (accept_3_5 2 43 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 63 (Polychromatic418967fa.accept_15_1_13_3_1_2002 1 43 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 63))))))))))))))))))))) (allB_succ' 22 42 63 (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 42 63 21 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 42 63 (Polychromatic418967fa.accept_12_8_6_3_1_366 20 42 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 63 (Polychromatic418967fa.accept_18_1_6_9_1_2001 19 42 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 63 3 6 14 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 63
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 42 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 42 63 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 42 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 42 63 3 5 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 42 63 7 2 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 42 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 63 3 4 14 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 63
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 42 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 63 (Polychromatic418967fa.accept_11_10_9_8_1_1974 10 42 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 42 63 3 3 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 42 63 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 42 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 42 63 7 1 6 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 42 63 3 2 14 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 63
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 42 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 63 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 42 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 42 63 3 1 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 42 63 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 42 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 63
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 42 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 42 63)))))))))))))))))))))) (allB_succ' 23 41 63 (Eq.refl Bool.true) (allA_succ_of_accept 22 41 63
  (accept_3_4 22 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 63
  (Polychromatic418967fa.accept_12_9_5_3_1_782 21 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 41 63 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 41 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 63 (accept_3_4 19 41 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 41 63 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 41 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 63 (Polychromatic418967fa.accept_13_4_2_11_1_733
  17 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 63 (accept_3_4 16 41
  63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 63
  (Polychromatic418967fa.accept_14_1_13_7_1_1205 15 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 41 63 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 41 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 63 (accept_3_4 13 41 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 41 63 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 41 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 63
  (Polychromatic418967fa.accept_25_11_16_13_1_2000 11 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 63 (accept_3_4 10 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 41
  63 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 41 63 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 41 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 63 (accept_3_4 7 41 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 41 63 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 41 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 63 (Polychromatic418967fa.accept_17_5_7_12_1_1951 5
  41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 63 (accept_3_4 4 41 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41 63 (Polychromatic418967fa.accept_13_3_2_11_1_1999 3
  41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 63
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 41 63 (accept_3_4 1 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41
  63))))))))))))))))))))))) (allB_succ' 24 40 63 (Eq.refl Bool.true) (allA_succ_of_accept 23 40 63 (accept_3_5 23 40 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 63 (Polychromatic418967fa.accept_13_9_1_11_1_275
  22 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 63
  (Polychromatic418967fa.accept_13_8_1_11_1_1284 21 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 63 (accept_3_5 20 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 40
  63 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 40 63 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 40 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 63 (accept_3_5 17 40 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 40 63 (Polychromatic418967fa.accept_13_3_1_11_1_1268 16 40 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 63 (Polychromatic418967fa.accept_11_4_7_8_1_1926
  15 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 40 63 (accept_3_5 14 40
  63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 40 63 (Polychromatic418967fa.accept_6_1_4_3_1_14
  13 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 40 63
  (Polychromatic418967fa.accept_13_12_1_11_1_1917 12 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 40 63 (accept_3_5 11 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 40
  63 (Polychromatic418967fa.accept_13_10_1_11_1_1961 10 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 40 63 (Polychromatic418967fa.accept_13_9_1_11_1_275 9 40 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 40 63 (accept_3_5 8 40 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 40 63 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 40 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 40 63 (Polychromatic418967fa.accept_12_6_4_3_1_361 6
  40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 63 (accept_3_5 5 40 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 40 63 (Polychromatic418967fa.accept_11_4_7_8_1_1926 4
  40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 63
  (Polychromatic418967fa.accept_13_3_1_11_1_1268 3 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 40 63 (accept_3_5 2 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 63
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 63)))))))))))))))))))))))) (allB_succ' 25 39 63 (Eq.refl Bool.true) (allA_succ_of_gcd 24 39 63 3 8 13 21
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 39 63
  (Polychromatic418967fa.accept_15_8_9_3_1_1194 23 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 39 63 (Polychromatic418967fa.accept_16_6_7_15_1_1942 22 39 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 63 3 7 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 63 (Polychromatic418967fa.accept_15_5_9_3_1_528 20 39 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 63
  (Polychromatic418967fa.accept_16_3_7_15_1_1130 19 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 39 63 3 6 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 39 63 (Polychromatic418967fa.accept_14_3_11_7_1_1260 17 39 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 63 (Polychromatic418967fa.accept_10_6_9_3_1_935 16 39 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 39 63 3 5 13 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 39 63
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 14 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 63 (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 39 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 63 3 4 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 63 (Polychromatic418967fa.accept_16_11_7_15_1_1998 11 39 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 63
  (Polychromatic418967fa.accept_14_10_11_7_1_1955 10 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 39 63 3 3 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 39 63 (Polychromatic418967fa.accept_15_8_9_3_1_1194 8 39 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 63 (Polychromatic418967fa.accept_17_7_5_12_1_1997 7 39 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 39 63 3 2 13 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 39 63
  (Polychromatic418967fa.accept_15_5_9_3_1_528 5 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 39 63 (Polychromatic418967fa.accept_10_4_9_3_1_1907 4 39 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 63 3 1 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 63 (Polychromatic418967fa.accept_18_2_3_9_1_1996 2 39 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 63
  (Polychromatic418967fa.accept_18_1_3_9_1_328 1 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 39 63))))))))))))))))))))))))) (allB_succ' 26 38 63 (Eq.refl Bool.true) (allA_succ_of_accept 25 38 63
  (accept_3_4 25 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 38 63
  (Polychromatic418967fa.accept_11_2_5_8_1_470 24 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 38 63 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 38 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 63 (accept_3_4 22 38 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 38 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 38 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 63 (Polychromatic418967fa.accept_13_7_12_11_1_1911
  20 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 38 63 (accept_3_4 19 38
  63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 38 63 (Polychromatic418967fa.accept_12_6_2_3_1_354
  18 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 38 63
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 38 63 (accept_3_4 16 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 38
  63 (Polychromatic418967fa.accept_10_5_8_3_1_229 15 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 38 63 (Polychromatic418967fa.accept_11_3_5_8_1_458 14 38 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 38 63 (accept_3_4 13 38 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 38 63 (Polychromatic418967fa.accept_15_12_8_3_1_1995 12 38 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 38 63 (Polychromatic418967fa.accept_6_5_2_3_1_81 11
  38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 63 (accept_3_4 10 38 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 38
  63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 63
  (Polychromatic418967fa.accept_17_8_4_12_1_1994 8 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 63 (accept_3_4 7 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38 63
  (Polychromatic418967fa.accept_10_6_8_3_1_930 6 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 63 (accept_3_4 4 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 38 63 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 38 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 63 (Polychromatic418967fa.accept_11_2_5_8_1_470 2 38 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 63 (accept_3_4 1 38 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 38 63)))))))))))))))))))))))))) (allB_succ' 27 37 63 (Eq.refl Bool.true)
  (allA_succ_of_accept 26 37 63 (accept_3_5 26 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37
  63 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 37 63 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 37 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 63 (accept_3_5 23 37 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 37 63 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 37 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 63 (Polychromatic418967fa.accept_12_9_1_3_1_350 21
  37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 63 (accept_3_5 20 37 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 63 (Polychromatic418967fa.accept_14_5_9_7_1_590 19
  37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 63
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 63 (accept_3_5 17 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 37
  63 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 37 63 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 37 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 63 (accept_3_5 14 37 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 37 63 (Polychromatic418967fa.accept_29_13_8_5_1_1993 13 37 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 63 (Polychromatic418967fa.accept_11_1_4_8_1_1918
  12 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 63 (accept_3_5 11 37
  63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 63 (Polychromatic418967fa.accept_4_2_1_3_1_27
  10 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 63
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 63 (accept_3_5 8 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 63
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 37 63 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 37 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 63 (accept_3_5 5 37 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 37 63 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 37 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 63 (Polychromatic418967fa.accept_18_3_1_9_1_1929 3
  37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 63 (accept_3_5 2 37 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 63 (Polychromatic418967fa.accept_11_1_4_8_1_1918 1
  37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 63)))))))))))))))))))))))))))
  (allB_succ' 28 36 63 (Eq.refl Bool.true) (allA_succ_of_gcd 27 36 63 9 3 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 36 63 (Polychromatic418967fa.accept_15_11_6_3_1_1192
  26 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 63
  (Polychromatic418967fa.accept_13_12_10_11_1_1279 25 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 36 63 3 8 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 36 63 (Polychromatic418967fa.accept_17_6_2_12_1_1992 23 36 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 63 (Polychromatic418967fa.accept_19_3_17_6_1_1991 22 36 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 36 63 3 7 12 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 36 63
  (Polychromatic418967fa.accept_14_6_8_7_1_589 20 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 36 63 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 36 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 63 9 2 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 63 (Polychromatic418967fa.accept_10_7_6_3_1_927 17 36 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 63
  (Polychromatic418967fa.accept_11_5_3_8_1_454 16 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 36 63 3 5 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 36 63 (Polychromatic418967fa.accept_13_1_10_11_1_1280 14 36 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 63 (Polychromatic418967fa.accept_14_13_8_7_1_1224 13 36 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 63 3 4 12 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 63
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 36 63 (Polychromatic418967fa.accept_15_10_6_3_1_1160 10 36 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 36 63 9 1 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 36 63 (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 36 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 63
  (Polychromatic418967fa.accept_10_7_6_3_1_927 7 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 36 63 3 2 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 36 63 (Polychromatic418967fa.accept_11_5_3_8_1_454 5 36 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36 63 (Polychromatic418967fa.accept_13_4_10_11_1_1908 4 36 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 36 63 3 1 12 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 36 63
  (Polychromatic418967fa.accept_13_2_10_11_1_1276 2 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 36 63 (Polychromatic418967fa.accept_13_1_10_11_1_1280 1 36 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 36 63)))))))))))))))))))))))))))) (allB_succ' 29 35 63 (Eq.refl Bool.true)
  (allA_succ_of_gcd 28 35 63 7 4 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 35 63 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 35 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 63 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 35 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 63 (accept_3_4 25 35 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 63 (Polychromatic418967fa.accept_15_9_5_3_1_554 24
  35 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 63
  (Polychromatic418967fa.accept_15_8_5_3_1_1990 23 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 63 (accept_3_4 22 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 35 63
  7 3 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 35 63
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 63 (accept_3_4 19 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 35
  63 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 35 63 (Polychromatic418967fa.accept_10_7_5_3_1_542 17 35 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 63 (accept_3_4 16 35 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 35 63 (Polychromatic418967fa.accept_13_2_9_11_1_258 15 35 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 35 63 7 2 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 35 63 (accept_3_4 13 35 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 63 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 35 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 63
  (Polychromatic418967fa.accept_16_11_3_15_1_1989 11 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 35 63 (accept_3_4 10 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 35
  63 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 35 63 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 35 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 35 63 7 1 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 35 63 (Polychromatic418967fa.accept_15_6_5_3_1_1988 6 35 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 63
  (Polychromatic418967fa.accept_11_5_2_8_1_866 5 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 35 63 (accept_3_4 4 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 63
  (Polychromatic418967fa.accept_19_3_16_6_1_1987 3 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 35 63 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 35 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 63 (accept_3_4 1 35 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 35 63))))))))))))))))))))))))))))) (allB_succ' 30 34 63 (Eq.refl Bool.true) (allA_succ_of_accept
  29 34 63 (accept_3_5 29 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 63
  (Polychromatic418967fa.accept_16_12_2_15_1_490 28 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 34 63 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 34 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 34 63 (accept_3_5 26 34 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 34 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 34 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 34 63 (Polychromatic418967fa.accept_19_5_15_6_1_1986
  24 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 63 (accept_3_5 23 34
  63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 63
  (Polychromatic418967fa.accept_13_9_8_11_1_725 22 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 34 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 34 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 34 63 (accept_3_5 20 34 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 34 63 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 34 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 34 63 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  18 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 63 (accept_3_5 17 34
  63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 63
  (Polychromatic418967fa.accept_13_3_8_11_1_1906 16 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 34 63 (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 34 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 34 63 (accept_3_5 14 34 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 34 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 34 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 34 63 (Polychromatic418967fa.accept_16_12_2_15_1_490
  12 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 63 (accept_3_5 11 34
  63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 63
  (Polychromatic418967fa.accept_13_10_8_11_1_1985 10 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 34 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 34 63 (accept_3_5 8 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 34 63 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 34 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 34 63 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 34 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 63 (accept_3_5 5 34 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 34 63 (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 34 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 63
  (Polychromatic418967fa.accept_13_3_8_11_1_1906 3 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 34 63 (accept_3_5 2 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 63
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 63)))))))))))))))))))))))))))))) (allB_succ' 31 33 63 (Eq.refl Bool.true) (allA_succ_of_gcd 30 33 63 3 10
  11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 33 63
  (Polychromatic418967fa.accept_12_5_9_3_1_85 29 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 63 (Polychromatic418967fa.accept_17_11_16_12_1_1984 28 33 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 63 3 9 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 63 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 33 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 63
  (Polychromatic418967fa.accept_12_1_9_3_1_370 25 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 33 63 3 8 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 33 63 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 33 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 63 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 33 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 33 63 3 7 11 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 33 63
  (Polychromatic418967fa.accept_19_1_14_6_1_1983 20 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 63 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 33 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 63 3 6 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 63 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 33 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 63
  (Polychromatic418967fa.accept_13_3_7_11_1_1904 16 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 33 63 3 5 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 33 63 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 33 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 63 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 33 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 33 63 3 4 11 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 33 63
  (Polychromatic418967fa.accept_12_11_9_3_1_792 11 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 33 63 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 33 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 63 3 3 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 63 (Polychromatic418967fa.accept_16_8_1_15_1_1982 8 33 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 63
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 33 63 3 2 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 33 63 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 33 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 63 (Polychromatic418967fa.accept_13_4_7_11_1_1981 4 33 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 33 63 3 1 11 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 33 63
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 33 63 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 33 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 33 63))))))))))))))))))))))))))))))) (allB_succ 32 63 (allA_succ_of_accept
  31 32 63 (accept_3_4 31 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 32 63
  (Polychromatic418967fa.accept_12_6_8_3_1_82 30 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 32 63 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 32 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 63 (accept_3_4 28 32 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 32 63 (Polychromatic418967fa.accept_15_12_2_3_1_1146 27 32 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 63 (Polychromatic418967fa.accept_19_7_13_6_1_1914
  26 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 32 63 (accept_3_4 25 32
  63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 32 63
  (Polychromatic418967fa.accept_14_10_4_7_1_1214 24 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 32 63 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 32 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 63 (accept_3_4 22 32 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 32 63 (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 32 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 63 (Polychromatic418967fa.accept_11_9_10_8_1_444
  20 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 32 63 (accept_3_4 19 32
  63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 32 63 (Polychromatic418967fa.accept_12_6_8_3_1_82
  18 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 32 63
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 32 63 (accept_3_4 16 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 32
  63 (Polychromatic418967fa.accept_10_5_2_3_1_239 15 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 32 63 (Polychromatic418967fa.accept_15_14_2_3_1_1980 14 32 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 32 63 (accept_3_4 13 32 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 32 63 (Polychromatic418967fa.accept_15_12_2_3_1_1146 12 32 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 32 63 (Polychromatic418967fa.accept_6_5_2_3_1_81 11
  32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 63 (accept_3_4 10 32 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 63 (Polychromatic418967fa.accept_11_9_10_8_1_444 9
  32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 63
  (Polychromatic418967fa.accept_13_8_6_11_1_1979 8 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 63 (accept_3_4 7 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32 63
  (Polychromatic418967fa.accept_12_6_8_3_1_82 6 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 63 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 32 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 63 (accept_3_4 4 32 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 63 (Polychromatic418967fa.accept_14_3_4_7_1_175 3 32 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 63 (Polychromatic418967fa.accept_19_2_13_6_1_1978 2
  32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 63 (accept_3_4 1 32 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 63)))))))))))))))))))))))))))))))) (allB_succ 31 63
  (allA_succ_of_accept 30 31 63 (Polychromatic418967fa.accept_20_10_11_3_1_1977 30 31 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 63 (accept_3_5 29 31 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 63 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 31 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 63 (Polychromatic418967fa.accept_19_8_12_6_1_1976
  27 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 63 (accept_3_5 26 31
  63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 63
  (Polychromatic418967fa.accept_14_11_3_7_1_604 25 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 31 63 (Polychromatic418967fa.accept_14_10_3_7_1_1975 24 31 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 63 (accept_3_5 23 31 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 31 63 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 31 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 63 (Polychromatic418967fa.accept_11_10_9_8_1_1974
  21 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 63 (accept_3_5 20 31
  63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 63
  (Polychromatic418967fa.accept_13_6_5_11_1_1971 19 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 31 63 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 31 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 63 (accept_3_5 17 31 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 31 63 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 31 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 63
  (Polychromatic418967fa.accept_17_15_14_12_1_1973 15 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 31 63 (accept_3_5 14 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31
  63 (Polychromatic418967fa.accept_15_13_1_3_1_1972 13 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 31 63 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 31 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 63 (accept_3_5 11 31 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 31 63 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 31 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 63
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 31 63 (accept_3_5 8 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 63
  (Polychromatic418967fa.accept_13_7_5_11_1_1927 7 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 31 63 (Polychromatic418967fa.accept_13_6_5_11_1_1971 6 31 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 63 (accept_3_5 5 31 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 31 63 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 31 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 63 (Polychromatic418967fa.accept_13_3_5_11_1_716 3
  31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 63 (accept_3_5 2 31 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 63 (Polychromatic418967fa.accept_25_1_6_13_1_1970 1
  31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 63)))))))))))))))))))))))))))))))
  (allB_succ 30 63 (allA_succ_of_accept 29 30 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 30 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 63 (Polychromatic418967fa.accept_12_4_6_3_1_332 28
  30 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 30 63 3 9 10 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 30 63
  (Polychromatic418967fa.accept_12_2_6_3_1_331 26 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 30 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 30 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 63 3 8 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 63 (Polychromatic418967fa.accept_13_10_4_11_1_1969 23 30 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 63
  (Polychromatic418967fa.accept_12_10_6_3_1_786 22 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 30 63 3 7 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 30 63 (Polychromatic418967fa.accept_12_8_6_3_1_366 20 30 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 63 (Polychromatic418967fa.accept_13_6_4_11_1_282 19 30 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 63 3 6 10 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 63
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 63 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 30 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 63 3 5 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 63 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 30 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 63
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 30 63 3 4 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 30 63 (Polychromatic418967fa.accept_17_11_13_12_1_1968 11 30 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 30 63 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 30 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 30 63 3 3 10 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 30 63
  (Polychromatic418967fa.accept_12_8_6_3_1_366 8 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 30 63 (Polychromatic418967fa.accept_13_7_4_11_1_1967 7 30 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 63 3 2 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 30 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30 63
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 30 63 3 1 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 30 63 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 30 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 30 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 63)))))))))))))))))))))))))))))) (allB_succ
  29 63 (allA_succ_of_accept 28 29 63 (accept_3_4 28 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 29 63 (Polychromatic418967fa.accept_13_1_3_11_1_1289 27 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 29 63 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 29 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 63 (accept_3_4 25 29 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 63 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 29 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 63
  (Polychromatic418967fa.accept_13_10_3_11_1_1923 23 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 63 (accept_3_4 22 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29
  63 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 29 63 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 29 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 63 (accept_3_4 19 29 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 29 63 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 29 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 63 (Polychromatic418967fa.accept_15_2_14_3_1_1916
  17 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 63 (accept_3_4 16 29
  63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 63
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 29 63 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 29 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 63 (accept_3_4 13 29 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 29 63 (Polychromatic418967fa.accept_16_12_13_15_1_1966 12 29 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 63
  (Polychromatic418967fa.accept_15_11_14_3_1_1965 11 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 63 (accept_3_4 10 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29
  63 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 29 63 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 29 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 63 (accept_3_4 7 29 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 29 63 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 29 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 63 (Polychromatic418967fa.accept_13_5_3_11_1_1288 5
  29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 63 (accept_3_4 4 29 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29 63 (Polychromatic418967fa.accept_16_3_13_15_1_1913
  3 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 63
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 29 63 (accept_3_4 1 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29
  63))))))))))))))))))))))))))))) (allB_succ 28 63 (allA_succ_of_accept 27 28 63
  (Polychromatic418967fa.accept_8_3_4_7_1_475 27 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 63 (accept_3_5 26 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 28
  63 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 28 63 (Polychromatic418967fa.accept_15_9_13_3_1_535 24 28 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 63 (accept_3_5 23 28 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 28 63 (Polychromatic418967fa.accept_13_9_2_11_1_1964 22 28 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 28 63 7 3 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 28 63 (accept_3_5 20 28 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 28 63 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 28 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 28 63
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 28 63 (accept_3_5 17 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 28
  63 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 28 63 (Polychromatic418967fa.accept_10_5_8_3_1_229 15 28 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 28 63 7 2 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 28 63 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 28 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 28 63
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 12 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 28 63 (accept_3_5 11 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 28
  63 (Polychromatic418967fa.accept_13_10_2_11_1_1920 10 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 28 63 (Polychromatic418967fa.accept_13_9_2_11_1_1964 9 28 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 28 63 (accept_3_5 8 28 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 7 28 63 7 1 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 6 28 63 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 28 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 63 (accept_3_5 5 28 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 28 63 (Polychromatic418967fa.accept_13_4_2_11_1_733 4 28 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 63 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 28
  63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 63 (accept_3_5 2 28 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 63 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 28
  63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 63)))))))))))))))))))))))))))) (allB_succ
  27 63 (allA_succ_of_accept 26 27 63 (Polychromatic418967fa.accept_10_6_7_3_1_547 26 27 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 63 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 27 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 63 3 8 9 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 63
  (Polychromatic418967fa.accept_13_10_1_11_1_1961 23 27 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 63 (Polychromatic418967fa.accept_13_9_1_11_1_275 22 27 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 27 63 3 7 9 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 27 63 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 27 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 63
  (Polychromatic418967fa.accept_16_3_11_15_1_1963 19 27 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 27 63 9 2 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 27 63 (Polychromatic418967fa.accept_15_2_12_3_1_1183 17 27 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 63 (Polychromatic418967fa.accept_10_6_7_3_1_547 16 27 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 63 3 5 9 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 63
  (Polychromatic418967fa.accept_10_4_7_3_1_54 14 27 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 63 (Polychromatic418967fa.accept_11_2_5_8_1_470 13 27 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 27 63 3 4 9 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 27 63 (Polychromatic418967fa.accept_23_11_4_17_1_1962 11 27 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 63
  (Polychromatic418967fa.accept_13_10_1_11_1_1961 10 27 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 27 63 9 1 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 27 63 (Polychromatic418967fa.accept_13_8_1_11_1_1284 8 27 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 63 (Polychromatic418967fa.accept_13_7_1_11_1_732 7 27 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 63 3 2 9 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 63
  (Polychromatic418967fa.accept_10_5_7_3_1_561 5 27 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 63 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 27 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 27 63 3 1 9 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 27 63 (Polychromatic418967fa.accept_11_2_5_8_1_470 2 27 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 63
  (Polychromatic418967fa.accept_14_1_13_7_1_1205 1 27 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 27 63))))))))))))))))))))))))))) (allB_succ 26 63 (allA_succ_of_accept 25 26 63 (accept_3_4 25 26 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 63 (Polychromatic418967fa.accept_18_6_8_9_1_1960
  24 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 26 63
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 26 63 (accept_3_4 22 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 26
  63 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 26 63 (Polychromatic418967fa.accept_19_1_7_6_1_1959 20 26 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 63 (accept_3_4 19 26 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 26 63 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 26 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 26 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 26
  63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 63 (accept_3_4 16 26 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 26 63 (Polychromatic418967fa.accept_22_15_4_19_1_1958
  15 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 63
  (Polychromatic418967fa.accept_15_14_11_3_1_1957 14 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 26 63 (accept_3_4 13 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 26
  63 (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 26 63 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 26 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 63 (accept_3_4 10 26 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 26 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 26 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 63 (Polychromatic418967fa.accept_10_8_6_3_1_1394 8
  26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 63 (accept_3_4 7 26 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26 63 (Polychromatic418967fa.accept_12_6_2_3_1_354 6
  26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 63
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 26 63 (accept_3_4 4 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26 63
  (Polychromatic418967fa.accept_18_3_8_9_1_1956 3 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 26 63 (Polychromatic418967fa.accept_14_2_12_7_1_617 2 26 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 63 (accept_3_4 1 26 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 26 63)))))))))))))))))))))))))) (allB_succ 25 63 (allA_succ_of_accept 24 25 63
  (Polychromatic418967fa.accept_14_10_11_7_1_1955 24 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 63 (accept_3_5 23 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 25
  63 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 25 63 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 25 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 63 (accept_3_5 20 25 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 25 63 (Polychromatic418967fa.accept_23_19_2_17_1_1954 19 25 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 63 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 63 (accept_3_5 17 25 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 25 63 (Polychromatic418967fa.accept_6_4_1_3_1_77 16
  25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 63
  (Polychromatic418967fa.accept_20_15_5_3_1_1953 15 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 25 63 (accept_3_5 14 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 25
  63 (Polychromatic418967fa.accept_15_13_10_3_1_1952 13 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 25 63 (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 25 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 63 (accept_3_5 11 25 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 25 63 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 25 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 63
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 63 (accept_3_5 8 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 63
  (Polychromatic418967fa.accept_10_7_5_3_1_542 7 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 25 63 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 25 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 63 (accept_3_5 5 25 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 25 63 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 25 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 63 (Polychromatic418967fa.accept_14_3_11_7_1_1260 3
  25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 63 (accept_3_5 2 25 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 63 (Polychromatic418967fa.accept_13_1_12_11_1_728 1
  25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 63))))))))))))))))))))))))) (allB_succ
  24 63 (allA_succ_of_accept 23 24 63 (Polychromatic418967fa.accept_15_8_9_3_1_1194 23 24 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 63 (Polychromatic418967fa.accept_17_5_7_12_1_1951
  22 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 24 63 3 7 8 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 24 63
  (Polychromatic418967fa.accept_15_5_9_3_1_528 20 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 63 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 24 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 63 3 6 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 63 (Polychromatic418967fa.accept_10_7_4_3_1_560 17 24 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 63
  (Polychromatic418967fa.accept_11_5_2_8_1_866 16 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 24 63 3 5 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 24 63 (Polychromatic418967fa.accept_18_14_6_9_1_1950 14 24 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 63 (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 24 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 63 3 4 8 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 63
  (Polychromatic418967fa.accept_14_11_10_7_1_1948 11 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 63 (Polychromatic418967fa.accept_15_10_9_3_1_1947 10 24 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 24 63 3 3 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 24 63 (Polychromatic418967fa.accept_15_8_9_3_1_1194 8 24 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 63
  (Polychromatic418967fa.accept_10_7_4_3_1_560 7 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 63 3 2 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 63 (Polychromatic418967fa.accept_11_5_2_8_1_866 5 24 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 63 (Polychromatic418967fa.accept_14_4_10_7_1_1946 4 24 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 24 63 3 1 8 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 24 63
  (Polychromatic418967fa.accept_17_2_7_12_1_1078 2 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 63 (Polychromatic418967fa.accept_16_1_8_15_1_1945 1 24 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 24 63)))))))))))))))))))))))) (allB_succ 23 63 (allA_succ_of_accept 22 23 63
  (accept_3_4 22 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 63
  (Polychromatic418967fa.accept_12_9_11_3_1_772 21 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 63 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 23 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 63 (accept_3_4 19 23 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 63 (Polychromatic418967fa.accept_17_1_6_12_1_1944 18 23 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 63 (Polychromatic418967fa.accept_13_4_10_11_1_1908
  17 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 63 (accept_3_4 16 23
  63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 63
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 23 63 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 23 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 63 (accept_3_4 13 23 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 23 63 (Polychromatic418967fa.accept_13_12_10_11_1_1279 12 23 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 63
  (Polychromatic418967fa.accept_15_11_8_3_1_1943 11 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 63 (accept_3_4 10 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 23
  63 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 23 63 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 23 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 63 (accept_3_4 7 23 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 23 63 (Polychromatic418967fa.accept_16_6_7_15_1_1942 6 23 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 63 (Polychromatic418967fa.accept_14_5_9_7_1_590 5
  23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 63 (accept_3_4 4 23 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 63 (Polychromatic418967fa.accept_13_3_10_11_1_1293
  3 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 63
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 23 63 (accept_3_4 1 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23
  63))))))))))))))))))))))) (allB_succ 22 63 (allA_succ_of_accept 21 22 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 22 63 (accept_3_5 20 22 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 22 63 (Polychromatic418967fa.accept_6_1_4_3_1_14 19
  22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 22 63
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 22 63 (accept_3_5 17 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 22
  63 (Polychromatic418967fa.accept_19_16_3_6_1_1941 16 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 22 63 (Polychromatic418967fa.accept_10_5_2_3_1_239 15 22 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 22 63 (accept_3_5 14 22 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 22 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 22 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 22 63
  (Polychromatic418967fa.accept_15_12_7_3_1_1940 12 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 22 63 (accept_3_5 11 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 22
  63 (Polychromatic418967fa.accept_15_10_7_3_1_1939 10 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 22 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 22 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 22 63 (accept_3_5 8 22 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 22 63 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 22 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 22 63 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6
  22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 63 (accept_3_5 5 22 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 22 63 (Polychromatic418967fa.accept_15_4_7_3_1_119 4
  22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 63
  (Polychromatic418967fa.accept_24_3_22_15_1_1938 3 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 22 63 (accept_3_5 2 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 63
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 22 63)))))))))))))))))))))) (allB_succ 21 63 (allA_succ_of_accept 20 21 63
  (Polychromatic418967fa.accept_11_9_10_8_1_444 20 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 63 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 21 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 63 3 6 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 63 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 21 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 63
  (Polychromatic418967fa.accept_13_3_8_11_1_1906 16 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 21 63 3 5 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 21 63 7 2 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 21 63 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 21 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 21 63 3 4 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 21 63 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 21 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 63
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 21 63 3 3 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 21 63 (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 21 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 21 63 7 1 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 21 63 3 2 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 63 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 21 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 63
  (Polychromatic418967fa.accept_13_4_8_11_1_1937 4 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 21 63 3 1 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 21 63 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 21 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 63 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 21 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 63))))))))))))))))))))) (allB_succ 20 63
  (allA_succ_of_accept 19 20 63 (accept_3_4 19 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20
  63 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 63 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 20 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 63 (accept_3_4 16 20 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 20 63 (Polychromatic418967fa.accept_14_1_6_7_1_1936 15 20 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 63 (Polychromatic418967fa.accept_13_1_7_11_1_702
  14 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 63 (accept_3_4 13 20
  63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 63
  (Polychromatic418967fa.accept_13_12_7_11_1_1935 12 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 20 63 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 20 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 63 (accept_3_4 10 20 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 20 63 (Polychromatic418967fa.accept_13_9_7_11_1_1292 9 20 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 63 (Polychromatic418967fa.accept_14_8_6_7_1_1934 8
  20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 63 (accept_3_4 7 20 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 63 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 20
  63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 20 63
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 20 63 (accept_3_4 4 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20 63
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 20 63 (Polychromatic418967fa.accept_15_2_5_3_1_552 2 20 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 63 (accept_3_4 1 20 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 63)))))))))))))))))))) (allB_succ 19 63 (allA_succ_of_accept 18 19 63
  (Polychromatic418967fa.accept_13_5_6_11_1_1933 18 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 63 (accept_3_5 17 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 19
  63 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 19 63 (Polychromatic418967fa.accept_25_15_19_13_1_1932 15 19 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 63 (accept_3_5 14 19 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 19 63 (Polychromatic418967fa.accept_16_13_3_15_1_1931 13 19 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 63 (Polychromatic418967fa.accept_8_4_3_7_1_491 12
  19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 19 63 (accept_3_5 11 19 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 19 63 (Polychromatic418967fa.accept_6_4_1_3_1_77 10
  19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 19 63
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 19 63 (accept_3_5 8 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 63
  (Polychromatic418967fa.accept_15_7_4_3_1_1930 7 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 19 63 (Polychromatic418967fa.accept_10_6_9_3_1_935 6 19 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 19 63 (accept_3_5 5 19 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 19 63 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 19 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 19 63 (Polychromatic418967fa.accept_18_3_1_9_1_1929 3
  19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 63 (accept_3_5 2 19 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 63 (Polychromatic418967fa.accept_15_1_4_3_1_1928 1
  19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 63))))))))))))))))))) (allB_succ 18 63
  (allA_succ_of_accept 17 18 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 18 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 63 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 18 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 18 63 3 5 6 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 18 63
  (Polychromatic418967fa.accept_12_2_6_3_1_331 14 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 18 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 18 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 63 3 4 6 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 63 (Polychromatic418967fa.accept_10_1_8_3_1_947 11 18 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 63
  (Polychromatic418967fa.accept_12_10_6_3_1_786 10 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 18 63 9 1 2 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 18 63 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 18 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 18 63 (Polychromatic418967fa.accept_13_7_5_11_1_1927 7 18 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 63 3 2 6 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 63
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 18 63 (Polychromatic418967fa.accept_11_4_7_8_1_1926 4 18 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 18 63 3 1 6 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 18 63 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 18 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 63
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 63)))))))))))))))))) (allB_succ 17 63 (allA_succ_of_accept 16 17 63 (accept_3_4 16 17 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 63 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 17 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 63
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 63 (accept_3_4 13 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 17
  63 (Polychromatic418967fa.accept_13_12_4_11_1_1925 12 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 63 (Polychromatic418967fa.accept_14_11_3_7_1_604 11 17 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 63 (accept_3_4 10 17 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 63 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 17 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 63
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 63 (accept_3_4 7 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 63
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 63 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 17 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 63 (accept_3_4 4 17 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 63 (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 17 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 63 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 17
  63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 63 (accept_3_4 1 17 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 63))))))))))))))))) (allB_succ 16 63 (allA_succ_of_accept 15 16
  63 (Polychromatic418967fa.accept_13_2_3_11_1_1287 15 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 16 63 (accept_3_5 14 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 16 63 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 16 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 16 63 (Polychromatic418967fa.accept_14_12_2_7_1_1243 12 16 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 63 (accept_3_5 11 16 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 63 (Polychromatic418967fa.accept_13_10_3_11_1_1923
  10 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 63
  (Polychromatic418967fa.accept_10_9_6_3_1_545 9 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 63 (accept_3_5 8 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16 63
  (Polychromatic418967fa.accept_6_1_4_3_1_14 7 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 16 63 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 16 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 63 (accept_3_5 5 16 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 16 63 (Polychromatic418967fa.accept_15_4_1_3_1_1922 4 16 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 63 (Polychromatic418967fa.accept_11_3_5_8_1_458 3
  16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 63 (accept_3_5 2 16 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 63 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 16
  63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 63)))))))))))))))) (allB_succ 15 63
  (allA_succ_of_accept 14 15 63 (Polychromatic418967fa.accept_17_14_15_12_1_1921 14 15 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 63 (Polychromatic418967fa.accept_14_13_1_7_1_1211 13 15 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 63 3 4 5 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 63
  (Polychromatic418967fa.accept_18_11_15_9_1_360 11 15 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 15 63 (Polychromatic418967fa.accept_13_10_2_11_1_1920 10 15 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 15 63 3 3 5 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 15 63 (Polychromatic418967fa.accept_10_8_5_3_1_543 8 15 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 63
  (Polychromatic418967fa.accept_10_7_5_3_1_542 7 15 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 15 63 3 2 5 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 15 63 (Polychromatic418967fa.accept_18_5_15_9_1_1919 5 15 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 63 (Polychromatic418967fa.accept_13_4_2_11_1_733 4 15 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 63 3 1 5 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 63
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 2 15 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 63 (Polychromatic418967fa.accept_11_1_4_8_1_1918 1 15 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 15 63))))))))))))))) (allB_succ 14 63 (allA_succ_of_accept 13 14 63
  (accept_3_4 13 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 63
  (Polychromatic418967fa.accept_13_12_1_11_1_1917 12 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 14 63 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 14 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 63 (accept_3_4 10 14 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 14 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 14 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 63 (Polychromatic418967fa.accept_13_8_1_11_1_1284 8
  14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 14 63 7 1 2 9 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 14 63
  (Polychromatic418967fa.accept_11_6_3_8_1_843 6 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 14 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 14 63 (accept_3_4 4 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 14 63 (Polychromatic418967fa.accept_13_3_1_11_1_1268 3 14 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 14 63 (Polychromatic418967fa.accept_15_2_14_3_1_1916 2 14 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 63 (accept_3_4 1 14 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 14 63)))))))))))))) (allB_succ 13 63 (allA_succ_of_accept 12 13 63
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 12 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 63 (accept_3_5 11 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 13
  63 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 13 63 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 13 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 63 (accept_3_5 8 13 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 13 63 (Polychromatic418967fa.accept_19_7_13_6_1_1914 7 13 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 63 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 13
  63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 13 63 (accept_3_5 5 13 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13 63 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 13
  63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 13 63
  (Polychromatic418967fa.accept_16_3_13_15_1_1913 3 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 13 63 (accept_3_5 2 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 63
  (Polychromatic418967fa.accept_14_1_13_7_1_1205 1 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 13 63))))))))))))) (allB_succ 12 63 (allA_succ_of_accept 11 12 63
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 12 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 12 63 (Polychromatic418967fa.accept_13_10_12_11_1_731 10 12 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 12 63 3 3 4 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 12 63 (Polychromatic418967fa.accept_15_8_12_3_1_1912 8 12 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 63
  (Polychromatic418967fa.accept_13_7_12_11_1_1911 7 12 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 12 63 3 2 4 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 12 63 (Polychromatic418967fa.accept_10_5_2_3_1_239 5 12 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 63 (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 12 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 12 63 3 1 4 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 12 63
  (Polychromatic418967fa.accept_14_2_12_7_1_617 2 12 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 12 63 (Polychromatic418967fa.accept_10_1_2_3_1_1910 1 12 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 63)))))))))))) (allB_succ 11 63 (allA_succ_of_accept 10 11 63 (accept_3_4
  10 11 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 63
  (Polychromatic418967fa.accept_12_9_11_3_1_772 9 11 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 63 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 11 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 63 (accept_3_4 7 11 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 63 (Polychromatic418967fa.accept_15_6_11_3_1_1172 6 11 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 63 (Polychromatic418967fa.accept_19_5_11_6_1_1909 5
  11 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 63 (accept_3_4 4 11 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 63 (Polychromatic418967fa.accept_14_3_11_7_1_1260 3
  11 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 63
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 11 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 63 (accept_3_4 1 11 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 63)))))))))))
  (allB_succ 10 63 (allA_succ_of_accept 9 10 63 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 10 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 63 (accept_3_5 8 10 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 10 63 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 10 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 63 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6
  10 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 10 63 (accept_3_5 5 10 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 10 63 (Polychromatic418967fa.accept_13_4_10_11_1_1908
  4 10 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 63
  (Polychromatic418967fa.accept_13_3_10_11_1_1293 3 10 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 10 63 (accept_3_5 2 10 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 63
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 10 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 10 63)))))))))) (allB_succ 9 63 (allA_succ_of_accept 8 9 63 (Polychromatic418967fa.accept_13_8_9_11_1_1265 8
  9 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 63
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 9 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 9 63 3 2 3 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 9 63 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 9 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 63 (Polychromatic418967fa.accept_10_4_9_3_1_1907 4 9 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 9 63 3 1 3 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 9 63
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 9 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 63 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 9 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 9 63))))))))) (allB_succ 8 63 (allA_succ_of_accept 7 8 63 (accept_3_4 7 8 63
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 63 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 8
  63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 63
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 8 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 8 63 (accept_3_4 4 8 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 63
  (Polychromatic418967fa.accept_13_3_8_11_1_1906 3 8 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 8 63 (Polychromatic418967fa.accept_19_2_8_6_1_1905 2 8 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 63 (accept_3_4 1 8 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 63)))))))) (allB_succ 7 63 (allA_succ_of_accept 6 7 63
  (Polychromatic418967fa.accept_10_6_7_3_1_547 6 7 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 63 (accept_3_5 5 7 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 63
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 7 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 63 (Polychromatic418967fa.accept_13_3_7_11_1_1904 3 7 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 63 (accept_3_5 2 7 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 63 (Polychromatic418967fa.accept_13_1_7_11_1_702 1 7 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 63))))))) (allB_succ 6 63 (allA_succ_of_accept 5 6 63
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 6 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 63 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 6 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 6 63 3 1 2 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 6 63 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 6 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 63
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 6 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 63)))))) (allB_succ 5 63 (allA_succ_of_accept 4 5 63 (accept_3_4 4 5 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 5 63 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 5 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 63 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 5 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 63 (accept_3_4 1 5 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 5 63))))) (allB_succ 4 63 (allA_succ_of_accept 3 4 63
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 4 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 63 (accept_3_5 2 4 63 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 63
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 4 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 63)))) (allB_succ 3 63 (allA_succ_of_accept 2 3 63 (Polychromatic418967fa.accept_13_2_3_11_1_1287 2 3 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 63
  (Polychromatic418967fa.accept_13_1_3_11_1_1289 1 3 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 3 63))) (allB_succ 2 63 (allA_succ_of_accept 1 2 63 (accept_3_4 1 2 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 2 63)) (allB_two 63)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


