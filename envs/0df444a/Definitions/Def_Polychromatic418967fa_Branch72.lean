-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch72
-- name    : Polychromatic418967fa_Branch72
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:08:54.520464+00:00
-- url     : https://prove2.me/theorems/4fb246c0-5654-4cee-9886-fcc28d27c6f0
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

def Polychromatic418967fa.branch_72 : allB 72 72 :=
  allB_succ' 2 71 72 (Eq.refl Bool.true) (allA_succ_of_accept 1 71 72 (accept_3_4 1 71 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 72)) (allB_succ' 3 70 72 (Eq.refl Bool.true) (allA_succ_of_gcd 2 70 72 2 1 35 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 72
  (Polychromatic418967fa.accept_27_1_16_18_1_2547 1 70 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 72))) (allB_succ' 4 69 72 (Eq.refl Bool.true) (allA_succ_of_gcd 3 69 72 3 1 23 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 72
  (Polychromatic418967fa.accept_20_2_9_12_1_2546 2 69 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 72 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 69 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 69 72)))) (allB_succ' 5 68 72 (Eq.refl Bool.true) (allA_succ_of_gcd 4 68 72
  4 1 17 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 68 72
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 68 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 68 72 2 1 34 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 68 72 (accept_3_4 1 68 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68 72)))))
  (allB_succ' 6 67 72 (Eq.refl Bool.true) (allA_succ_of_accept 5 67 72 (accept_3_5 5 67 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 67 72 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 67 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 67 72 (Polychromatic418967fa.accept_15_3_7_12_1_372 3
  67 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 72 (accept_3_5 2 67 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 72 (Polychromatic418967fa.accept_23_1_21_3_1_2545 1
  67 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67 72)))))) (allB_succ' 7 66 72 (Eq.refl
  Bool.true) (allA_succ_of_gcd 6 66 72 6 1 11 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 66 72 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 66 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 72 2 2 33 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 66 72 3 1 22 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 66 72 2 1 33 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 72 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 66
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66 72))))))) (allB_succ' 8 65 72 (Eq.refl
  Bool.true) (allA_succ_of_accept 7 65 72 (accept_3_4 7 65 72 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 65 72 (Polychromatic418967fa.accept_15_6_5_12_1_1642 6 65 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 72 (Polychromatic418967fa.accept_11_5_10_6_1_793 5 65 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 72 (accept_3_4 4 65 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 72 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 65 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 72
  (Polychromatic418967fa.accept_15_2_5_12_1_369 2 65 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 65 72 (accept_3_4 1 65 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65 72))))))))
  (allB_succ' 9 64 72 (Eq.refl Bool.true) (allA_succ_of_gcd 8 64 72 8 1 8 9 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 64 72 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 64
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 72 2 3 32 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 72 (accept_3_5 5 64
  72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 72 4 1 16 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 64 72
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 64 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 64 72 2 1 32 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 64 72 (Polychromatic418967fa.accept_14_1_8_2_1_1675 1 64 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 64 72))))))))) (allB_succ' 10 63 72 (Eq.refl Bool.true) (allA_succ_of_gcd 9
  63 72 9 1 7 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8
  63 72 (Polychromatic418967fa.accept_15_8_3_12_1_1657 8 63 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 63 72 (Polychromatic418967fa.accept_15_7_3_12_1_365 7 63 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 63 72 3 2 21 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 72 (Polychromatic418967fa.accept_10_5_3_2_1_899 5 63
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 72
  (Polychromatic418967fa.accept_13_4_11_7_1_558 4 63 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 63 72 3 1 21 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 63 72 (Polychromatic418967fa.accept_15_2_3_12_1_891 2 63 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 72 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 63 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63 72)))))))))) (allB_succ' 11 62 72 (Eq.refl
  Bool.true) (allA_succ_of_gcd 10 62 72 2 5 31 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 62 72 (Polychromatic418967fa.accept_19_9_5_15_1_2544 9 62 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 72 2 4 31 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 72 (accept_3_4 7 62 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 62 72 2 3 31 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 62 72 (Polychromatic418967fa.accept_15_5_2_12_1_2543 5 62 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 72 2 2 31 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 72 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 62
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 62 72 2 1 31 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 62 72 (accept_3_4 1 62
  72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62 72))))))))))) (allB_succ' 12 61 72 (Eq.refl Bool.true)
  (allA_succ_of_accept 11 61 72 (accept_3_5 11 61 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 61
  72 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 61 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 61 72 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 61 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 72 (accept_3_5 8 61 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 61 72 (Polychromatic418967fa.accept_14_7_5_2_1_2473 7 61 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 72 (Polychromatic418967fa.accept_10_6_1_2_1_874 6
  61 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 61 72 (accept_3_5 5 61 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61 72 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 61
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 61 72
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 61 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 61 72 (accept_3_5 2 61 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 72
  (Polychromatic418967fa.accept_19_1_4_15_1_2542 1 61 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 61 72)))))))))))) (allB_succ' 13 60 72 (Eq.refl Bool.true) (allA_succ_of_gcd 12 60 72 12 1 5 6 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 72
  (Polychromatic418967fa.accept_16_11_12_8_1_1592 11 60 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 60 72 2 5 30 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 60 72 3 3 20 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 60 72 4 2 15 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 60 72 (Polychromatic418967fa.accept_16_7_12_8_1_2450 7 60 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 72 6 1 10 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 72 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 60 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 72 4 1 15 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 60 72 3 1 20 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 60 72 2 1 30 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 72
  (Polychromatic418967fa.accept_11_1_5_6_1_397 1 60 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 60 72))))))))))))) (allB_succ' 14 59 72 (Eq.refl Bool.true) (allA_succ_of_accept 13 59 72 (accept_3_4 13 59
  72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 72 (Polychromatic418967fa.accept_7_5_3_2_1_249
  12 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 72
  (Polychromatic418967fa.accept_10_1_9_2_1_45 11 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 72 (accept_3_4 10 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 59
  72 (Polychromatic418967fa.accept_15_9_14_12_1_913 9 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 59 72 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 59 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 72 (accept_3_4 7 59 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 59 72 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 59 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 72 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 59
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 72 (accept_3_4 4 59 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 72 (Polychromatic418967fa.accept_16_3_11_8_1_830 3
  59 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 72
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 2 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 59 72 (accept_3_4 1 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59
  72)))))))))))))) (allB_succ' 15 58 72 (Eq.refl Bool.true) (allA_succ_of_gcd 14 58 72 2 7 29 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 58 72
  (Polychromatic418967fa.accept_21_13_16_9_1_2541 13 58 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 58 72 2 6 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 58 72 (accept_3_5 11 58 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 72
  2 5 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 58 72
  (Polychromatic418967fa.accept_11_9_3_6_1_797 9 58 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 58 72 2 4 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 58 72 (Polychromatic418967fa.accept_21_7_16_9_1_2417 7 58 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 72 2 3 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 72 (accept_3_5 5 58 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 58 72 2 2 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 58 72 (Polychromatic418967fa.accept_15_3_13_12_1_348 3 58 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 72 2 1 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 72 (Polychromatic418967fa.accept_13_1_6_7_1_550 1 58
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58 72))))))))))))))) (allB_succ' 16 57 72
  (Eq.refl Bool.true) (allA_succ_of_gcd 15 57 72 3 5 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 57 72 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 57 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 72
  (Polychromatic418967fa.accept_7_6_1_2_1_230 13 57 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 57 72 3 4 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 57 72 (Polychromatic418967fa.accept_13_11_5_7_1_2420 11 57 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 72 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 57 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 72 3 3 19 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 72
  (Polychromatic418967fa.accept_14_8_1_2_1_965 8 57 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 72 (Polychromatic418967fa.accept_16_7_9_8_1_829 7 57 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 57 72 3 2 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 57 72 (Polychromatic418967fa.accept_10_5_7_2_1_516 5 57 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 72
  (Polychromatic418967fa.accept_10_4_7_2_1_211 4 57 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 57 72 3 1 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 57 72 (Polychromatic418967fa.accept_13_2_5_7_1_1695 2 57 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 72 (Polychromatic418967fa.accept_16_1_9_8_1_2438 1 57 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 72)))))))))))))))) (allB_succ' 17 56 72
  (Eq.refl Bool.true) (allA_succ_of_gcd 16 56 72 8 2 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 56 72 (Polychromatic418967fa.accept_21_15_14_9_1_2540 15 56 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 72 2 7 28 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 72 (accept_3_4 13 56 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 72 4 3 14 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 56 72 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 56 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 56 72 2 5 28 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 56 72
  (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 56 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 56 72 8 1 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 56 72 (accept_3_4 7 56 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 72 2
  3 28 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 56 72
  (Polychromatic418967fa.accept_11_5_1_6_1_774 5 56 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 56 72 4 1 14 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 56 72 (Polychromatic418967fa.accept_13_3_4_7_1_1711 3 56 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 72 2 1 28 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 72 (accept_3_4 1 56 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 56 72))))))))))))))))) (allB_succ' 18 55 72 (Eq.refl Bool.true) (allA_succ_of_accept 17 55 72
  (accept_3_5 17 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 72
  (Polychromatic418967fa.accept_21_16_13_9_1_2539 16 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 55 72 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 55 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 72 (accept_3_5 14 55 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 55 72 (Polychromatic418967fa.accept_10_3_5_2_1_38 13 55 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 72 (Polychromatic418967fa.accept_16_12_7_8_1_1589
  12 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 72 (accept_3_5 11 55
  72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 55 72 (Polychromatic418967fa.accept_7_3_6_2_1_90
  10 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 72
  (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 72 (accept_3_5 8 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 72
  (Polychromatic418967fa.accept_10_7_5_2_1_880 7 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 55 72 (Polychromatic418967fa.accept_15_6_10_12_1_2538 6 55 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 72 (accept_3_5 5 55 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 55 72 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 55 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 72 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 55
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 72 (accept_3_5 2 55 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 72 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 55
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 72)))))))))))))))))) (allB_succ' 19 54 72
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 54 72 18 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 54 72 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 54 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 72 2 8 27 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 54 72 3 5 18 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 54 72 2 7 27 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 72
  (Polychromatic418967fa.accept_17_13_3_4_1_2537 13 54 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 54 72 6 2 9 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 54 72 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 54 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 72 2 5 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 54 72 9 1 6 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 54 72 2 4 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 72 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 54 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 72 6 1 9 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 72
  (Polychromatic418967fa.accept_11_5_10_6_1_793 5 54 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 54 72 2 2 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 54 72 3 1 18 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 54 72 2 1 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 54 72 (Polychromatic418967fa.accept_19_1_16_15_1_2536 1 54 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 54 72))))))))))))))))))) (allB_succ' 20 53 72 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 53 72 (accept_3_4 19 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 53
  72 (Polychromatic418967fa.accept_15_3_8_12_1_900 18 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 53 72 (Polychromatic418967fa.accept_25_17_3_22_1_2535 17 53 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 72 (accept_3_4 16 53 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 53 72 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 53 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 72 (Polychromatic418967fa.accept_11_3_9_6_1_105 14
  53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 72 (accept_3_4 13 53 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 72 (Polychromatic418967fa.accept_7_5_4_2_1_235 12
  53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 72
  (Polychromatic418967fa.accept_10_1_3_2_1_220 11 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 72 (accept_3_4 10 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 53
  72 (Polychromatic418967fa.accept_14_9_11_2_1_2501 9 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 53 72 (Polychromatic418967fa.accept_13_8_1_7_1_2505 8 53 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 72 (accept_3_4 7 53 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 53 72 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 53 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 72 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 53
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 72 (accept_3_4 4 53 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53 72 (Polychromatic418967fa.accept_11_3_9_6_1_105 3
  53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 72
  (Polychromatic418967fa.accept_21_2_11_9_1_2534 2 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 53 72 (accept_3_4 1 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53
  72)))))))))))))))))))) (allB_succ' 21 52 72 (Eq.refl Bool.true) (allA_succ_of_gcd 20 52 72 4 5 13 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 52 72
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 52 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 52 72 2 9 26 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 52 72 (accept_3_5 17 52 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52 72
  4 4 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 52
  72 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 52 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 52 72 2 7 26 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 52 72 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 52 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 52 72 4 3 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 52 72 (accept_3_5 11 52 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 52 72 2 5 26 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 52 72 (Polychromatic418967fa.accept_16_9_4_8_1_2533 9 52 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 52 72 4 2 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 52 72 (Polychromatic418967fa.accept_16_7_4_8_1_2487 7
  52 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 72 2 3 26 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 72 (accept_3_5 5 52
  72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 72 4 1 13 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 52 72
  (Polychromatic418967fa.accept_11_3_8_6_1_788 3 52 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 52 72 2 1 26 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 52 72 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 52 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 52 72))))))))))))))))))))) (allB_succ' 22 51 72 (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 51 72 3 7 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 51 72 (Polychromatic418967fa.accept_15_5_6_12_1_916 20 51 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 72 (Polychromatic418967fa.accept_10_9_1_2_1_522 19 51 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 51 72 3 6 17 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 51 72
  (Polychromatic418967fa.accept_13_4_12_7_1_2439 17 51 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 51 72 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 51 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 72 3 5 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 72 (Polychromatic418967fa.accept_19_14_13_15_1_2532 14 51 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 72
  (Polychromatic418967fa.accept_10_3_1_2_1_521 13 51 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 51 72 3 4 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 51 72 (Polychromatic418967fa.accept_13_11_12_7_1_2443 11 51 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 72 (Polychromatic418967fa.accept_13_10_12_7_1_1079 10 51 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 51 72 3 3 17 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 51 72
  (Polychromatic418967fa.accept_13_8_12_7_1_2442 8 51 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 72 (Polychromatic418967fa.accept_14_7_9_2_1_2489 7 51 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 72 3 2 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 72 (Polychromatic418967fa.accept_13_5_12_7_1_1080 5 51 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 72
  (Polychromatic418967fa.accept_13_4_12_7_1_2439 4 51 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 51 72 3 1 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 51 72 (Polychromatic418967fa.accept_15_2_6_12_1_1613 2 51 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 72 (Polychromatic418967fa.accept_11_1_7_6_1_378 1 51 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 72)))))))))))))))))))))) (allB_succ' 23 50
  72 (Eq.refl Bool.true) (allA_succ_of_gcd 22 50 72 2 11 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 50 72 (Polychromatic418967fa.accept_15_6_5_12_1_1642 21 50 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 72 2 10 25 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 72 (accept_3_4 19 50 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50 72 2 9 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 50 72 (Polychromatic418967fa.accept_7_3_1_2_1_247 17
  50 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 72 2 8 25 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 72
  (Polychromatic418967fa.accept_14_1_8_2_1_1675 15 50 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 50 72 2 7 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 50 72 (accept_3_4 13 50 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50 72
  2 6 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 50
  72 (Polychromatic418967fa.accept_32_11_18_8_1_2531 11 50 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 50 72 2 5 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 50 72 (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 50 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 72 2 4 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 72 (accept_3_4 7 50 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 50 72 2 3 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 50 72 (Polychromatic418967fa.accept_13_5_11_7_1_559 5 50 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 72 2 2 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 72 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 50
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 72 2 1 25 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 72 (accept_3_4 1 50
  72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 72))))))))))))))))))))))) (allB_succ' 24 49 72 (Eq.refl
  Bool.true) (allA_succ_of_accept 23 49 72 (accept_3_5 23 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 49 72 (Polychromatic418967fa.accept_15_7_4_12_1_2530 22 49 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 72 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 49 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 72 (accept_3_5 20 49 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 72 (Polychromatic418967fa.accept_14_5_7_2_1_468 19
  49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 72
  (Polychromatic418967fa.accept_21_18_7_9_1_2529 18 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 72 (accept_3_5 17 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 49
  72 (Polychromatic418967fa.accept_13_3_10_7_1_1061 16 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 72 (Polychromatic418967fa.accept_16_15_1_8_1_1585 15 49 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 72 (accept_3_5 14 49 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 72 (Polychromatic418967fa.accept_21_13_7_9_1_2528 13 49 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 72
  (Polychromatic418967fa.accept_11_1_5_6_1_397 12 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 72 (accept_3_5 11 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 49
  72 (Polychromatic418967fa.accept_11_10_5_6_1_1842 10 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 72 (Polychromatic418967fa.accept_14_9_7_2_1_2483 9 49 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 72 (accept_3_5 8 49 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 49 72 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 49 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 72 (Polychromatic418967fa.accept_19_6_11_15_1_2527
  6 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 72 (accept_3_5 5 49 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49 72 (Polychromatic418967fa.accept_13_4_10_7_1_1701 4
  49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 72
  (Polychromatic418967fa.accept_13_3_10_7_1_1061 3 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 49 72 (accept_3_5 2 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 72
  (Polychromatic418967fa.accept_10_1_9_2_1_45 1 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 49 72)))))))))))))))))))))))) (allB_succ' 25 48 72 (Eq.refl Bool.true) (allA_succ_of_gcd 24 48 72 24 1 2 3
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 72
  (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 48 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 48 72 2 11 24 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 48 72 3 7 16 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 48 72 4 5 12 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 48 72 (Polychromatic418967fa.accept_13_6_9_7_1_2430 19 48 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 72 6 3 8 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 72 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 48 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 72 8 2 6 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 48 72 3 5 16 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 48 72 2 7 24 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 72
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 13 48 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 48 72 12 1 4 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 48 72 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 48 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 72 2 5 24 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 48 72 3 3 16 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 48 72 8 1 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 72 (Polychromatic418967fa.accept_15_7_3_12_1_365 7 48 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 72 6 1 8 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 72
  (Polychromatic418967fa.accept_10_5_8_2_1_517 5 48 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 48 72 4 1 12 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 48 72 3 1 16 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 48 72 2 1 24 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 48 72 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 48 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 48 72))))))))))))))))))))))))) (allB_succ' 26 47 72 (Eq.refl Bool.true)
  (allA_succ_of_accept 25 47 72 (accept_3_4 25 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 47
  72 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 47 72 (Polychromatic418967fa.accept_13_10_8_7_1_1074 23 47 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 72 (accept_3_4 22 47 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 47 72 (Polychromatic418967fa.accept_14_7_5_2_1_2473 21 47 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 72 (Polychromatic418967fa.accept_11_9_3_6_1_797 20
  47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 72 (accept_3_4 19 47 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 72 (Polychromatic418967fa.accept_7_4_5_2_1_243 18
  47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 72
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 72 (accept_3_4 16 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 47
  72 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 47 72 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 47 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 72 (accept_3_4 13 47 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 47 72 (Polychromatic418967fa.accept_13_12_8_7_1_2526 12 47 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 72 (Polychromatic418967fa.accept_7_4_5_2_1_243 11
  47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 72 (accept_3_4 10 47 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 72 (Polychromatic418967fa.accept_10_9_7_2_1_887 9
  47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 72
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 8 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 72 (accept_3_4 7 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 72
  (Polychromatic418967fa.accept_15_6_2_12_1_885 6 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 47 72 (Polychromatic418967fa.accept_10_5_7_2_1_516 5 47 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 72 (accept_3_4 4 47 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 47 72 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 47 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 72 (Polychromatic418967fa.accept_13_2_8_7_1_2424 2
  47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 72 (accept_3_4 1 47 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47 72)))))))))))))))))))))))))) (allB_succ' 27 46 72 (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 46 72 2 13 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 46 72 (Polychromatic418967fa.accept_17_8_12_4_1_2525 25 46 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 72 2 12 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 72 (accept_3_5 23 46 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 72 2 11 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 46 72 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 46 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 46 72 2 10 23 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 46 72
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 46 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 46 72 2 9 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 46 72 (accept_3_5 17 46 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46 72
  2 8 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 46
  72 (Polychromatic418967fa.accept_11_4_2_6_1_389 15 46 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 46 72 2 7 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 46 72 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 46 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 72 2 6 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 72 (accept_3_5 11 46 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 46 72 2 5 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 46 72 (Polychromatic418967fa.accept_14_9_4_2_1_983 9 46 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 46 72 2 4 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 46 72 (Polychromatic418967fa.accept_17_7_12_4_1_2524 7
  46 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 72 2 3 23 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 72 (accept_3_5 5 46
  72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 46 72 2 2 23 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 46 72
  (Polychromatic418967fa.accept_19_3_8_15_1_2523 3 46 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 46 72 2 1 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 46 72 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 46 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 46 72))))))))))))))))))))))))))) (allB_succ' 28 45 72 (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 45 72 9 3 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 45 72 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 45 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 72 (Polychromatic418967fa.accept_13_12_6_7_1_1071 25 45 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 72 3 8 15 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 72
  (Polychromatic418967fa.accept_10_3_5_2_1_38 23 45 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 45 72 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 45 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 45 72 3 7 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 45 72 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 45 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 72
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 45 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 45 72 9 2 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 45 72 (Polychromatic418967fa.accept_10_7_5_2_1_880 17 45 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 72 (Polychromatic418967fa.accept_11_5_1_6_1_774 16 45 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 72 3 5 15 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 72
  (Polychromatic418967fa.accept_13_1_6_7_1_550 14 45 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 72 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 45 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 45 72 3 4 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 45 72 (Polychromatic418967fa.accept_16_11_13_8_1_1578 11 45 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 72
  (Polychromatic418967fa.accept_17_10_11_4_1_2522 10 45 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 45 72 9 1 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 45 72 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 45 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 72 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 45 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 72 3 2 15 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 72
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 45 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 45 72 (Polychromatic418967fa.accept_13_4_6_7_1_2471 4 45 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 45 72 3 1 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 45 72 (Polychromatic418967fa.accept_21_2_3_9_1_1317 2 45 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 72
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 45 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 45 72)))))))))))))))))))))))))))) (allB_succ' 29 44 72 (Eq.refl Bool.true) (allA_succ_of_gcd 28 44 72 4 7 11
  18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 44 72
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 44 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 44 72 2 13 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 44 72 (accept_3_4 25 44 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44 72
  4 6 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 44
  72 (Polychromatic418967fa.accept_16_7_12_8_1_2450 23 44 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 44 72 2 11 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 44 72 (Polychromatic418967fa.accept_16_5_12_8_1_2521 21 44 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 72 4 5 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 72 (accept_3_4 19 44 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44 72 2 9 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 44 72 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 44 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 44 72 4 4 11 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 44 72
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 15 44 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 44 72 2 7 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 44 72 (accept_3_4 13 44 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 72
  4 3 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 44
  72 (Polychromatic418967fa.accept_13_11_5_7_1_2420 11 44 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 44 72 2 5 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 44 72 (Polychromatic418967fa.accept_15_9_14_12_1_913 9 44 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 72 4 2 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 72 (accept_3_4 7 44 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 44 72 2 3 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 44 72 (Polychromatic418967fa.accept_16_5_12_8_1_2521 5 44 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 44 72 4 1 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 44 72 (Polychromatic418967fa.accept_16_3_12_8_1_808 3
  44 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 72 2 1 22 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 72 (accept_3_4 1 44
  72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 72))))))))))))))))))))))))))))) (allB_succ' 30 43 72 (Eq.refl
  Bool.true) (allA_succ_of_accept 29 43 72 (accept_3_5 29 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 43 72 (Polychromatic418967fa.accept_16_12_11_8_1_832 28 43 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 72 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 43 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 72 (accept_3_5 26 43 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 72 (Polychromatic418967fa.accept_10_5_3_2_1_899 25
  43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 72
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 72 (accept_3_5 23 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 43
  72 (Polychromatic418967fa.accept_13_9_4_7_1_1694 22 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 43 72 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 43 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 72 (accept_3_5 20 43 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 43 72 (Polychromatic418967fa.accept_13_6_4_7_1_2464 19 43 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 72 (Polychromatic418967fa.accept_15_3_13_12_1_348
  18 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 72 (accept_3_5 17 43
  72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 72
  (Polychromatic418967fa.accept_11_5_10_6_1_793 16 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 43 72 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 43 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 72 (accept_3_5 14 43 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 43 72 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 43 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 72 (Polychromatic418967fa.accept_13_12_4_7_1_2520
  12 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 72 (accept_3_5 11 43
  72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 72 (Polychromatic418967fa.accept_7_3_1_2_1_247
  10 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 72
  (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 72 (accept_3_5 8 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 72
  (Polychromatic418967fa.accept_22_7_21_6_1_2519 7 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 43 72 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 43 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 72 (accept_3_5 5 43 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 43 72 (Polychromatic418967fa.accept_16_4_11_8_1_1574 4 43 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 72 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 43
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 72 (accept_3_5 2 43 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 72 (Polychromatic418967fa.accept_10_1_3_2_1_220 1
  43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 72))))))))))))))))))))))))))))))
  (allB_succ' 31 42 72 (Eq.refl Bool.true) (allA_succ_of_gcd 30 42 72 6 5 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 72 (Polychromatic418967fa.accept_17_12_8_4_1_2518
  29 42 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 72 2 14 21 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 42 72 3 9 14 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 42 72 2 13 21 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 72
  (Polychromatic418967fa.accept_11_3_9_6_1_105 25 42 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 72 6 4 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 72 (Polychromatic418967fa.accept_13_10_3_7_1_2517 23 42 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 72 2 11 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 42 72 3 7 14 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 42 72 2 10 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 72 (Polychromatic418967fa.accept_20_19_2_12_1_2516 19 42 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 72 6 3 7 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 72
  (Polychromatic418967fa.accept_13_4_3_7_1_2515 17 42 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 42 72 2 8 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 42 72 3 5 14 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 42 72 2 7 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 42 72 (Polychromatic418967fa.accept_17_13_8_4_1_2514 13 42 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 72 6 2 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 72 (Polychromatic418967fa.accept_13_11_3_7_1_2513 11 42 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 72 2 5 21 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 42 72 3 3 14 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 42 72 2 4 21 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 72
  (Polychromatic418967fa.accept_17_7_8_4_1_1520 7 42 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 42 72 6 1 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 42 72 (Polychromatic418967fa.accept_19_5_4_15_1_2512 5 42 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 72 2 2 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 42 72 3 1 14 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 42 72 2 1 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 72 (Polychromatic418967fa.accept_13_1_3_7_1_1710 1 42 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 72)))))))))))))))))))))))))))))))
  (allB_succ' 32 41 72 (Eq.refl Bool.true) (allA_succ_of_accept 31 41 72 (accept_3_4 31 41 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 72 (Polychromatic418967fa.accept_22_8_19_6_1_2511 30 41 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 72
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 72 (accept_3_4 28 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 41
  72 (Polychromatic418967fa.accept_19_8_3_15_1_2510 27 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 72 (Polychromatic418967fa.accept_10_6_1_2_1_874 26 41 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 72 (accept_3_4 25 41 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 72 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 41 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 72
  (Polychromatic418967fa.accept_10_3_1_2_1_521 23 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 72 (accept_3_4 22 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 41
  72 (Polychromatic418967fa.accept_13_8_2_7_1_2452 21 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 41 72 (Polychromatic418967fa.accept_16_4_9_8_1_2509 20 41 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 72 (accept_3_4 19 41 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 41 72 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 41 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 72 (Polychromatic418967fa.accept_7_3_6_2_1_90 17
  41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 72 (accept_3_4 16 41 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 72 (Polychromatic418967fa.accept_7_1_6_2_1_18 15
  41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 72
  (Polychromatic418967fa.accept_11_3_8_6_1_788 14 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 72 (accept_3_4 13 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 41
  72 (Polychromatic418967fa.accept_16_12_9_8_1_2508 12 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 72 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 41 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 72 (accept_3_4 10 41 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 72 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 41 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 72
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 72 (accept_3_4 7 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 72
  (Polychromatic418967fa.accept_10_6_1_2_1_874 6 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 72 (Polychromatic418967fa.accept_13_5_2_7_1_2414 5 41 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 72 (accept_3_4 4 41 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 72 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 41 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 72 (Polychromatic418967fa.accept_21_2_20_9_1_2507 2
  41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 72 (accept_3_4 1 41 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 72)))))))))))))))))))))))))))))))) (allB_succ' 33 40 72 (Eq.refl
  Bool.true) (allA_succ_of_gcd 32 40 72 8 4 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 40 72 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 40 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 40 72 2 15 20 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 40 72 (accept_3_5 29 40 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40 72 4 7 10 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 40 72 (Polychromatic418967fa.accept_17_10_6_4_1_2506 27 40 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 40 72 2 13 20 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 40 72
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 40 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 40 72 8 3 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 40 72 (accept_3_5 23 40 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40 72
  2 11 20 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 40
  72 (Polychromatic418967fa.accept_13_8_1_7_1_2505 21 40 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 40 72 4 5 10 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 40 72 (Polychromatic418967fa.accept_13_6_1_7_1_1690 19 40 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 72 2 9 20 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 72 (accept_3_5 17 40 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 40 72 8 2 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 40 72 (Polychromatic418967fa.accept_21_15_19_9_1_2504 15 40 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 40 72 2 7 20 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 40 72 (Polychromatic418967fa.accept_15_13_10_12_1_2503
  13 40 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 72 4 3 10 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 72 (accept_3_5 11 40
  72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 72 2 5 20 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 72
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 9 40 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 40 72 8 1 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 40 72 (Polychromatic418967fa.accept_14_7_12_2_1_2502 7 40 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 72 2 3 20 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 72 (accept_3_5 5 40 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 40 72 4 1 10 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 40 72 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 40 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 72 2 1 20 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 72 (Polychromatic418967fa.accept_11_1_7_6_1_378 1 40
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40 72)))))))))))))))))))))))))))))))))
  (allB_succ' 34 39 72 (Eq.refl Bool.true) (allA_succ_of_gcd 33 39 72 3 11 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 39 72 (Polychromatic418967fa.accept_21_11_18_9_1_465
  32 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 72
  (Polychromatic418967fa.accept_10_1_9_2_1_45 31 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 39 72 3 10 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 39 72 (Polychromatic418967fa.accept_15_14_9_12_1_2498 29 39 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 72 (Polychromatic418967fa.accept_16_12_7_8_1_1589 28 39 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 72 3 9 13 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 72
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 72 (Polychromatic418967fa.accept_15_10_9_12_1_2497 25 39 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 39 72 3 8 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 39 72 (Polychromatic418967fa.accept_14_9_11_2_1_2501 23 39 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 72
  (Polychromatic418967fa.accept_20_2_19_12_1_2500 22 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 39 72 3 7 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 39 72 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 39 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 72 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 39 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 72 3 6 13 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 72
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 17 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 39 72 (Polychromatic418967fa.accept_17_16_5_4_1_2499 16 39 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 39 72 3 5 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 39 72 (Polychromatic418967fa.accept_15_14_9_12_1_2498 14 39 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 72
  (Polychromatic418967fa.accept_7_6_4_2_1_236 13 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 39 72 3 4 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 39 72 (Polychromatic418967fa.accept_10_1_9_2_1_45 11 39 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 72 (Polychromatic418967fa.accept_15_10_9_12_1_2497 10 39 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 72 3 3 13 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 72
  (Polychromatic418967fa.accept_19_8_1_15_1_2496 8 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 72 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 39 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 39 72 3 2 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 39 72 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 39 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 72
  (Polychromatic418967fa.accept_15_4_9_12_1_2495 4 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 39 72 3 1 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 39 72 (Polychromatic418967fa.accept_19_2_1_15_1_2494 2 39 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 72 (Polychromatic418967fa.accept_10_1_9_2_1_45 1 39 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 72))))))))))))))))))))))))))))))))))
  (allB_succ' 35 38 72 (Eq.refl Bool.true) (allA_succ_of_gcd 34 38 72 2 17 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 38 72 (Polychromatic418967fa.accept_7_5_3_2_1_249 33
  38 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 72 2 16 19 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 72 (accept_3_4 31 38
  72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 72 2 15 19 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 72
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 38 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 72 2 14 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 38 72 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 38 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 72 2 13 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 72 (accept_3_4 25 38 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 38 72 2 12 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 38 72 (Polychromatic418967fa.accept_11_1_5_6_1_397 23 38 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 72 2 11 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 72 (Polychromatic418967fa.accept_11_10_5_6_1_1842
  21 38 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 38 72 2 10 19 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 38 72 (accept_3_4 19 38
  72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38 72 2 9 19 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 38 72
  (Polychromatic418967fa.accept_13_4_12_7_1_2439 17 38 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 38 72 2 8 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 38 72 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 38 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 72 2 7 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 72 (accept_3_4 13 38 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 38 72 2 6 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 38 72 (Polychromatic418967fa.accept_13_11_12_7_1_2443 11 38 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 38 72 2 5 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 38 72 (Polychromatic418967fa.accept_22_9_16_6_1_2493 9
  38 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 38 72 2 4 19 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 38 72 (accept_3_4 7 38
  72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 72 2 3 19 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38 72
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 38 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 38 72 2 2 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 38 72 (Polychromatic418967fa.accept_15_3_8_12_1_900 3 38 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 72 2 1 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 72 (accept_3_4 1 38 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 38 72))))))))))))))))))))))))))))))))))) (allB_succ' 36 37 72 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 37 72 (accept_3_5 35 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 37
  72 (Polychromatic418967fa.accept_10_4_7_2_1_211 34 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 37 72 (Polychromatic418967fa.accept_15_3_7_12_1_372 33 37 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 72 (accept_3_5 32 37 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 37 72 (Polychromatic418967fa.accept_13_5_11_7_1_559 31 37 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 72 (Polychromatic418967fa.accept_13_4_11_7_1_558
  30 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 72 (accept_3_5 29 37
  72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 37 72
  (Polychromatic418967fa.accept_16_12_5_8_1_2492 28 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 37 72 (Polychromatic418967fa.accept_13_1_11_7_1_1704 27 37 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 72 (accept_3_5 26 37 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 37 72 (Polychromatic418967fa.accept_10_5_7_2_1_516 25 37 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 72 (Polychromatic418967fa.accept_10_4_7_2_1_211 24
  37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 72 (accept_3_5 23 37 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 37 72 (Polychromatic418967fa.accept_13_9_11_7_1_1077
  22 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 72
  (Polychromatic418967fa.accept_14_7_9_2_1_2489 21 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 37 72 (accept_3_5 20 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37
  72 (Polychromatic418967fa.accept_10_9_7_2_1_887 19 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 37 72 (Polychromatic418967fa.accept_13_5_11_7_1_559 18 37 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 72 (accept_3_5 17 37 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 37 72 (Polychromatic418967fa.accept_13_3_11_7_1_2488 16 37 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 72 (Polychromatic418967fa.accept_10_5_7_2_1_516 15
  37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 72 (accept_3_5 14 37 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 72 (Polychromatic418967fa.accept_11_2_4_6_1_2412
  13 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 72
  (Polychromatic418967fa.accept_13_12_11_7_1_2491 12 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 72 (accept_3_5 11 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 37
  72 (Polychromatic418967fa.accept_15_10_7_12_1_2490 10 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 72 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 37 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 72 (accept_3_5 8 37 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 37 72 (Polychromatic418967fa.accept_14_7_9_2_1_2489 7 37 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 72 (Polychromatic418967fa.accept_15_6_7_12_1_869 6
  37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 72 (accept_3_5 5 37 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37 72 (Polychromatic418967fa.accept_10_4_7_2_1_211 4
  37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 72
  (Polychromatic418967fa.accept_13_3_11_7_1_2488 3 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 37 72 (accept_3_5 2 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 72
  (Polychromatic418967fa.accept_13_1_11_7_1_1704 1 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 37 72)))))))))))))))))))))))))))))))))))) (allB_succ 36 72 (allA_succ_of_accept 35 36 72
  (Polychromatic418967fa.accept_15_5_6_12_1_916 35 36 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 36 72 2 17 18 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 36 72 3 11 12 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 36 72 4 8 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 36 72 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 36 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 72 6 5 6 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 72 (Polychromatic418967fa.accept_13_3_10_7_1_1061 29 36 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 72 4 7 9 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 36 72 9 3 4 8 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 36 72 2 13 18 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 72
  (Polychromatic418967fa.accept_13_12_10_7_1_2433 25 36 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 36 72 12 2 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 36 72 (Polychromatic418967fa.accept_16_7_4_8_1_2487 23 36 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 72 2 11 18 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 36 72 3 7 12 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 36 72 4 5 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 72 (Polychromatic418967fa.accept_11_8_3_6_1_1855 19 36 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 72 18 1 2 4 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 72
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 36 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 36 72 4 4 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 36 72 3 5 12 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 36 72 2 7 18 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 36 72 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 36 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 72 12 1 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 72 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 36 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 72 2 5 18 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 36 72 9 1 4 8 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 36 72 4 2 9 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 72
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 7 36 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 36 72 6 1 6 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 36 72 (Polychromatic418967fa.accept_15_5_6_12_1_916 5 36 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 72 4 1 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 36 72 3 1 12 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 36 72 2 1 18 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 72 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 36 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 72))))))))))))))))))))))))))))))))))))
  (allB_succ 35 72 (allA_succ_of_accept 34 35 72 (accept_3_4 34 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 35 72 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 35 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 72 (Polychromatic418967fa.accept_13_6_9_7_1_2430 32 35 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 72 (accept_3_4 31 35 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 35 72 (Polychromatic418967fa.accept_13_4_9_7_1_2402
  30 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 72
  (Polychromatic418967fa.accept_13_3_9_7_1_1730 29 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 35 72 (accept_3_4 28 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35
  72 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 72 (Polychromatic418967fa.accept_11_4_2_6_1_389 26 35 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 72 (accept_3_4 25 35 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 72 (Polychromatic418967fa.accept_13_11_9_7_1_2484 24 35 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 72 (Polychromatic418967fa.accept_10_3_5_2_1_38 23
  35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 72 (accept_3_4 22 35 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 72 (Polychromatic418967fa.accept_13_8_9_7_1_530 21
  35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 72
  (Polychromatic418967fa.accept_16_4_3_8_1_2486 20 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 72 (accept_3_4 19 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 35
  72 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 35 72 (Polychromatic418967fa.accept_10_7_5_2_1_880 17 35 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 72 (accept_3_4 16 35 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 35 72 (Polychromatic418967fa.accept_11_4_2_6_1_389 15 35 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 72 (Polychromatic418967fa.accept_17_14_1_4_1_2485
  14 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 72 (accept_3_4 13 35
  72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 72
  (Polychromatic418967fa.accept_14_12_7_2_1_1663 12 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 35 72 (Polychromatic418967fa.accept_13_11_9_7_1_2484 11 35 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 72 (accept_3_4 10 35 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 35 72 (Polychromatic418967fa.accept_14_9_7_2_1_2483 9 35 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 72 (Polychromatic418967fa.accept_10_8_5_2_1_881 8
  35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 72 (accept_3_4 7 35 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 72 (Polychromatic418967fa.accept_13_6_9_7_1_2430 6
  35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 72
  (Polychromatic418967fa.accept_14_5_7_2_1_468 5 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 35 72 (accept_3_4 4 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 72
  (Polychromatic418967fa.accept_10_3_5_2_1_38 3 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 35 72 (Polychromatic418967fa.accept_13_2_9_7_1_164 2 35 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 72 (accept_3_4 1 35 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 35 72))))))))))))))))))))))))))))))))))) (allB_succ 34 72 (allA_succ_of_accept 33 34 72
  (Polychromatic418967fa.accept_21_12_13_9_1_2482 33 34 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 34 72 2 16 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 34 72 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 34 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 72 2 15 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 72 (accept_3_5 29 34 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 34 72 2 14 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 34 72 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 34 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 72 2 13 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 72 (Polychromatic418967fa.accept_7_4_6_2_1_451 25
  34 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 34 72 2 12 17 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 34 72 (accept_3_5 23 34
  72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34 72 2 11 17 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 34 72
  (Polychromatic418967fa.accept_27_21_7_18_1_2481 21 34 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 34 72 2 10 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 34 72 (Polychromatic418967fa.accept_22_19_12_6_1_2480 19 34 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 72 2 9 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 72 (accept_3_5 17 34 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 34 72 2 8 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 34 72 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 34 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 72 2 7 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 72 (Polychromatic418967fa.accept_25_13_9_22_1_2479
  13 34 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 34 72 2 6 17 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 34 72 (accept_3_5 11 34
  72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34 72 2 5 17 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 34 72
  (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 34 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 34 72 2 4 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 34 72 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 34 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 72 2 3 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 72 (accept_3_5 5 34 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 34 72 2 2 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 34 72 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 34 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 72 2 1 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 72 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 34
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 72))))))))))))))))))))))))))))))))))
  (allB_succ 33 72 (allA_succ_of_accept 32 33 72 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 33 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 72
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 33 72 3 10 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 33 72 (Polychromatic418967fa.accept_19_10_14_15_1_2478 29 33 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 72 (Polychromatic418967fa.accept_15_13_3_12_1_1609 28 33 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 72 3 9 11 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 72
  (Polychromatic418967fa.accept_19_7_14_15_1_2477 26 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 72 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 33 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 72 3 8 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 72 (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 33 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 72
  (Polychromatic418967fa.accept_15_7_3_12_1_365 22 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 33 72 3 7 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 33 72 (Polychromatic418967fa.accept_16_4_1_8_1_835 20 33 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 72 (Polychromatic418967fa.accept_20_19_13_12_1_2476 19 33
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 72 3 6 11 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 72
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 72 (Polychromatic418967fa.accept_21_16_12_9_1_2475 16 33 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 72 3 5 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 72 (Polychromatic418967fa.accept_25_14_8_22_1_2474 14 33 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 72
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 33 72 3 4 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 33 72 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 33 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 72 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 33 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 72 3 3 11 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 72
  (Polychromatic418967fa.accept_15_8_3_12_1_1657 8 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 72 (Polychromatic418967fa.accept_14_7_5_2_1_2473 7 33 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 72 3 2 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 72 (Polychromatic418967fa.accept_10_5_3_2_1_899 5 33 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 72
  (Polychromatic418967fa.accept_7_4_5_2_1_243 4 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 33 72 3 1 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 33 72 (Polychromatic418967fa.accept_15_2_3_12_1_891 2 33 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 72 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 33 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 72)))))))))))))))))))))))))))))))))
  (allB_succ 32 72 (allA_succ_of_accept 31 32 72 (accept_3_4 31 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 32 72 2 15 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 32 72 (Polychromatic418967fa.accept_15_14_2_12_1_2472 29 32 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 32 72 4 7 8 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 32 72 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 32 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 72 2 13 16 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 72 (accept_3_4 25 32 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 72 8 3 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 72 (Polychromatic418967fa.accept_14_9_4_2_1_983 23
  32 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 72 2 11 16 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 72
  (Polychromatic418967fa.accept_15_6_2_12_1_885 21 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 72 4 5 8 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 72 (accept_3_4 19 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32 72
  2 9 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 32
  72 (Polychromatic418967fa.accept_13_4_6_7_1_2471 17 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 32 72 8 2 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 32 72 (Polychromatic418967fa.accept_21_15_11_9_1_2470 15 32 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 72 2 7 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 72 (accept_3_4 13 32 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 32 72 4 3 8 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 32 72 (Polychromatic418967fa.accept_17_11_15_4_1_2415 11 32 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 72 2 5 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 72 (Polychromatic418967fa.accept_13_9_6_7_1_551 9 32
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 32 72 8 1 4 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 32 72 (accept_3_4 7 32 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 72 2 3 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32 72 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 32 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 32 72 4 1 8 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 32 72
  (Polychromatic418967fa.accept_15_3_2_12_1_2469 3 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 32 72 2 1 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 32 72 (accept_3_4 1 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32
  72)))))))))))))))))))))))))))))))) (allB_succ 31 72 (allA_succ_of_accept 30 31 72
  (Polychromatic418967fa.accept_17_13_14_4_1_2468 30 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 72 (accept_3_5 29 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 31
  72 (Polychromatic418967fa.accept_13_2_5_7_1_1695 28 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 31 72 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 31 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 72 (accept_3_5 26 31 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 31 72 (Polychromatic418967fa.accept_11_3_9_6_1_105 25 31 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 72 (Polychromatic418967fa.accept_13_11_5_7_1_2420
  24 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 72 (accept_3_5 23 31
  72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 31 72 (Polychromatic418967fa.accept_7_1_3_2_1_13
  22 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 72
  (Polychromatic418967fa.accept_20_1_11_12_1_2467 21 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 31 72 (accept_3_5 20 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31
  72 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 31 72 (Polychromatic418967fa.accept_17_1_14_4_1_1550 18 31 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 72 (accept_3_5 17 31 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 31 72 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 31 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 72 (Polychromatic418967fa.accept_7_1_3_2_1_13 15
  31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 72 (accept_3_5 14 31 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 72 (Polychromatic418967fa.accept_7_6_3_2_1_461 13
  31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 72
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 72 (accept_3_5 11 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 31
  72 (Polychromatic418967fa.accept_27_10_4_18_1_2466 10 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 72 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 31 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 72 (accept_3_5 8 31 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 31 72 (Polychromatic418967fa.accept_16_7_15_8_1_278 7 31 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 72 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 31
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 72 (accept_3_5 5 31 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31 72 (Polychromatic418967fa.accept_15_4_1_12_1_914 4
  31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 72
  (Polychromatic418967fa.accept_10_3_1_2_1_521 3 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 31 72 (accept_3_5 2 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 72
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 31 72))))))))))))))))))))))))))))))) (allB_succ 30 72 (allA_succ_of_accept 29 30 72
  (Polychromatic418967fa.accept_13_3_4_7_1_1711 29 30 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 30 72 2 14 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 30 72 3 9 10 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 30 72 2 13 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 30 72 (Polychromatic418967fa.accept_11_3_8_6_1_788 25 30 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 72 6 4 5 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 72 (Polychromatic418967fa.accept_13_10_4_7_1_2465 23 30 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 72 2 11 15 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 30 72 3 7 10 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 30 72 2 10 15 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 72
  (Polychromatic418967fa.accept_13_6_4_7_1_2464 19 30 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 30 72 6 3 5 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 30 72 (Polychromatic418967fa.accept_22_17_8_6_1_2463 17 30 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 72 2 8 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 30 72 3 5 10 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 30 72 2 7 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 72 (Polychromatic418967fa.accept_20_13_10_12_1_2462 13 30 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 72 6 2 5 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 72
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 11 30 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 30 72 2 5 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 30 72 3 3 10 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 30 72 2 4 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 72 (Polychromatic418967fa.accept_19_7_11_15_1_2461 7 30 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 72 6 1 5 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 72 (Polychromatic418967fa.accept_19_5_11_15_1_2460 5 30 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 30 72 2 2 15 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 30 72 3 1 10 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 30 72 2 1 15 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 72
  (Polychromatic418967fa.accept_19_1_11_15_1_2459 1 30 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 30 72)))))))))))))))))))))))))))))) (allB_succ 29 72 (allA_succ_of_accept 28 29 72 (accept_3_4 28 29 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 72 (Polychromatic418967fa.accept_7_6_1_2_1_230 27
  29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 72
  (Polychromatic418967fa.accept_15_11_14_12_1_2458 26 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 29 72 (accept_3_4 25 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 29
  72 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 29 72 (Polychromatic418967fa.accept_11_1_7_6_1_378 23 29 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 72 (accept_3_4 22 29 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 29 72 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 29 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 72 (Polychromatic418967fa.accept_7_6_1_2_1_230 20
  29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 72 (accept_3_4 19 29 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 72 (Polychromatic418967fa.accept_21_18_8_9_1_2457
  18 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 72
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 72 (accept_3_4 16 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29
  72 (Polychromatic418967fa.accept_28_15_1_16_1_2456 15 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 72 (Polychromatic418967fa.accept_13_1_3_7_1_1710 14 29 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 72 (accept_3_4 13 29 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 72 (Polychromatic418967fa.accept_11_1_7_6_1_378 12 29 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 72
  (Polychromatic418967fa.accept_10_1_9_2_1_45 11 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 72 (accept_3_4 10 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29
  72 (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 29 72 (Polychromatic418967fa.accept_13_8_3_7_1_2455 8 29 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 72 (accept_3_4 7 29 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 29 72 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 29 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 72 (Polychromatic418967fa.accept_16_5_13_8_1_2454 5
  29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 72 (accept_3_4 4 29 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29 72 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 29
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 72
  (Polychromatic418967fa.accept_15_2_14_12_1_2453 2 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 29 72 (accept_3_4 1 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29
  72))))))))))))))))))))))))))))) (allB_succ 28 72 (allA_succ_of_accept 27 28 72
  (Polychromatic418967fa.accept_16_11_12_8_1_1592 27 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 28 72 2 13 14 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 28 72 (Polychromatic418967fa.accept_10_5_8_2_1_517 25 28 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 72 4 6 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 72 (accept_3_5 23 28 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 28 72 2 11 14 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 28 72 (Polychromatic418967fa.accept_13_8_2_7_1_2452 21 28 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 28 72 4 5 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 28 72 (Polychromatic418967fa.accept_16_3_12_8_1_808 19
  28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 28 72 2 9 14 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 28 72 (accept_3_5 17 28
  72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28 72 4 4 7 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 28 72
  (Polychromatic418967fa.accept_10_5_8_2_1_517 15 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 28 72 2 7 14 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 28 72 (Polychromatic418967fa.accept_16_13_12_8_1_2451 13 28 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 72 4 3 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 72 (accept_3_5 11 28 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 28 72 2 5 14 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 28 72 (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 28 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 28 72 4 2 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 28 72 (Polychromatic418967fa.accept_16_7_12_8_1_2450 7
  28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 28 72 2 3 14 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 72 (accept_3_5 5 28
  72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 72 4 1 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 28 72 (Polychromatic418967fa.accept_15_3_13_12_1_348 3
  28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 28 72 2 1 14 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 28 72
  (Polychromatic418967fa.accept_15_1_13_12_1_347 1 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 28 72)))))))))))))))))))))))))))) (allB_succ 27 72 (allA_succ_of_accept 26 27 72
  (Polychromatic418967fa.accept_19_7_8_15_1_2448 26 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 72 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 27 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 72 3 8 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 72 (Polychromatic418967fa.accept_11_1_5_6_1_397 23 27 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 72
  (Polychromatic418967fa.accept_7_1_6_2_1_18 22 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 27 72 3 7 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 27 72 (Polychromatic418967fa.accept_16_4_11_8_1_1574 20 27 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 72 (Polychromatic418967fa.accept_10_9_7_2_1_887 19 27 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 72 9 2 3 8 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 72
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 72 (Polychromatic418967fa.accept_13_3_1_7_1_1706 16 27 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 72 3 5 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 72 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 27 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 72
  (Polychromatic418967fa.accept_16_13_11_8_1_2449 13 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 27 72 3 4 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 27 72 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 27 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 72 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 27 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 72 9 1 3 8 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 72
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 72 (Polychromatic418967fa.accept_19_7_8_15_1_2448 7 27 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 72 3 2 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 72 (Polychromatic418967fa.accept_10_5_7_2_1_516 5 27 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 72
  (Polychromatic418967fa.accept_7_4_6_2_1_451 4 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 27 72 3 1 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 27 72 (Polychromatic418967fa.accept_19_2_8_15_1_2447 2 27 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 72 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 27 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 72))))))))))))))))))))))))))) (allB_succ 26
  72 (allA_succ_of_accept 25 26 72 (accept_3_4 25 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26
  72 2 12 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  26 72 (Polychromatic418967fa.accept_15_8_11_12_1_1626 23 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 72 2 11 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 26 72 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 26 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 72 2 10 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 72 (accept_3_4 19 26 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 72 2 9 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 26 72 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 26 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 72 2 8 13 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 72
  (Polychromatic418967fa.accept_20_15_6_12_1_2446 15 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 72 2 7 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 26 72 (accept_3_4 13 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26 72
  2 6 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 26
  72 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 26 72 2 5 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 26 72 (Polychromatic418967fa.accept_22_9_4_6_1_2445 9 26 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 72 2 4 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 72 (accept_3_4 7 26 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 26 72 2 3 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 26 72 (Polychromatic418967fa.accept_20_5_6_12_1_2444 5 26 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 72 2 2 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 72 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 26
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 26 72 2 1 13 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 26 72 (accept_3_4 1 26
  72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26 72)))))))))))))))))))))))))) (allB_succ 25 72
  (allA_succ_of_accept 24 25 72 (Polychromatic418967fa.accept_13_11_12_7_1_2443 24 25 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 72 (accept_3_5 23 25 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 72 (Polychromatic418967fa.accept_15_7_10_12_1_2403 22 25 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 72 (Polychromatic418967fa.accept_13_8_12_7_1_2442
  21 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 72 (accept_3_5 20 25
  72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 72 (Polychromatic418967fa.accept_7_5_4_2_1_235
  19 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 72
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 72 (accept_3_5 17 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 25
  72 (Polychromatic418967fa.accept_19_16_6_15_1_2441 16 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 72 (Polychromatic418967fa.accept_16_15_9_8_1_2440 15 25 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 72 (accept_3_5 14 25 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 72 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 25 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 72
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 72 (accept_3_5 11 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 25
  72 (Polychromatic418967fa.accept_13_10_12_7_1_1079 10 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 72 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 25 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 72 (accept_3_5 8 25 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 25 72 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 25 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 72 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 25
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 72 (accept_3_5 5 25 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25 72 (Polychromatic418967fa.accept_13_4_12_7_1_2439 4
  25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 72
  (Polychromatic418967fa.accept_10_3_5_2_1_38 3 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 25 72 (accept_3_5 2 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 72
  (Polychromatic418967fa.accept_16_1_9_8_1_2438 1 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 25 72))))))))))))))))))))))))) (allB_succ 24 72 (allA_succ_of_accept 23 24 72
  (Polychromatic418967fa.accept_19_4_5_15_1_2437 23 24 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 24 72 2 11 12 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 24 72 3 7 8 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 24 72 4 5 6 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 72 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 24 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 72 6 3 4 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 72 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 24 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 72 8 2 3 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 24 72 3 5 8 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 24 72 2 7 12 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 72
  (Polychromatic418967fa.accept_7_6_3_2_1_461 13 24 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 24 72 12 1 2 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 24 72 (Polychromatic418967fa.accept_19_11_5_15_1_2436 11 24 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 72 2 5 12 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 24 72 3 3 8 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 24 72 8 1 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 72 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 24 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 72 6 1 4 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 72
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 24 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 24 72 4 1 6 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 24 72 3 1 8 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 24 72 2 1 12 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 24 72 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 24 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 24 72)))))))))))))))))))))))) (allB_succ 23 72 (allA_succ_of_accept 22 23 72
  (accept_3_4 22 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 72
  (Polychromatic418967fa.accept_10_1_3_2_1_220 21 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 72 (Polychromatic418967fa.accept_15_5_8_12_1_2435 20 23 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 72 (accept_3_4 19 23 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 72 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 23 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 72 (Polychromatic418967fa.accept_13_4_10_7_1_1701
  17 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 72 (accept_3_4 16 23
  72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 72 (Polychromatic418967fa.accept_10_5_3_2_1_899
  15 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 72
  (Polychromatic418967fa.accept_19_14_4_15_1_2434 14 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 72 (accept_3_4 13 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23
  72 (Polychromatic418967fa.accept_13_12_10_7_1_2433 12 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 72 (Polychromatic418967fa.accept_10_1_3_2_1_220 11 23 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 72 (accept_3_4 10 23 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 72 (Polychromatic418967fa.accept_16_9_7_8_1_1588 9 23 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 72
  (Polychromatic418967fa.accept_13_8_10_7_1_1702 8 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 72 (accept_3_4 7 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 72
  (Polychromatic418967fa.accept_19_6_4_15_1_2432 6 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 72 (Polychromatic418967fa.accept_10_5_3_2_1_899 5 23 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 72 (accept_3_4 4 23 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 72 (Polychromatic418967fa.accept_13_3_10_7_1_1061 3 23 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 72 (Polychromatic418967fa.accept_17_2_6_4_1_2431 2
  23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 72 (accept_3_4 1 23 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 72))))))))))))))))))))))) (allB_succ 22 72 (allA_succ_of_accept
  21 22 72 (Polychromatic418967fa.accept_13_8_9_7_1_530 21 22 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 22 72 2 10 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 22 72 (Polychromatic418967fa.accept_13_6_9_7_1_2430 19 22 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 72 2 9 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 72 (accept_3_5 17 22 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 22 72 2 8 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 22 72 (Polychromatic418967fa.accept_13_2_9_7_1_164 15 22 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 72 2 7 11 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 72
  (Polychromatic418967fa.accept_7_6_1_2_1_230 13 22 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 22 72 2 6 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 22 72 (accept_3_5 11 22 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22 72
  2 5 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 22 72
  (Polychromatic418967fa.accept_19_9_3_15_1_2429 9 22 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 22 72 2 4 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 22 72 (Polychromatic418967fa.accept_19_7_3_15_1_2428 7 22 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 72 2 3 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 72 (accept_3_5 5 22 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 22 72 2 2 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 22 72 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 22 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 72 2 1 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 72 (Polychromatic418967fa.accept_14_1_8_2_1_1675 1
  22 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 72)))))))))))))))))))))) (allB_succ 21
  72 (allA_succ_of_accept 20 21 72 (Polychromatic418967fa.accept_15_5_6_12_1_916 20 21 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 72 (Polychromatic418967fa.accept_10_9_1_2_1_522 19 21 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 72 3 6 7 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 72
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 17 21 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 72 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 21 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 72 3 5 7 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 21 72 (Polychromatic418967fa.accept_13_1_8_7_1_1088 14 21 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 72
  (Polychromatic418967fa.accept_10_3_1_2_1_521 13 21 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 21 72 3 4 7 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 21 72 (Polychromatic418967fa.accept_16_11_5_8_1_2427 11 21 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 72 (Polychromatic418967fa.accept_13_10_8_7_1_1074 10 21 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 72 3 3 7 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 72
  (Polychromatic418967fa.accept_19_8_2_15_1_2426 8 21 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 72 (Polychromatic418967fa.accept_15_7_6_12_1_1614 7 21 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 21 72 3 2 7 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 72 (Polychromatic418967fa.accept_11_5_10_6_1_793 5 21 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 72
  (Polychromatic418967fa.accept_16_4_5_8_1_2425 4 21 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 21 72 3 1 7 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 21 72 (Polychromatic418967fa.accept_13_2_8_7_1_2424 2 21 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 72 (Polychromatic418967fa.accept_13_1_8_7_1_1088 1 21 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 72))))))))))))))))))))) (allB_succ 20 72
  (allA_succ_of_accept 19 20 72 (accept_3_4 19 20 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 72
  2 9 10 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20
  72 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 20 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 72 4 4 5 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 20 72 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 20 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 72 2 7 10 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 72 (accept_3_4 13 20 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 20 72 4 3 5 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 20 72 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 20 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 72 2 5 10 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 72 (Polychromatic418967fa.accept_15_9_5_12_1_1640 9
  20 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 20 72 4 2 5 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 20 72 (accept_3_4 7 20
  72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 72 2 3 10 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20 72
  (Polychromatic418967fa.accept_16_5_4_8_1_1560 5 20 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 20 72 4 1 5 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 20 72 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 20 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 72 2 1 10 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 72 (accept_3_4 1 20 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 72)))))))))))))))))))) (allB_succ 19 72 (allA_succ_of_accept 18 19 72
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 72 (accept_3_5 17 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 19
  72 (Polychromatic418967fa.accept_15_1_4_12_1_2401 16 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 72 (Polychromatic418967fa.accept_17_15_2_4_1_2423 15 19 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 72 (accept_3_5 14 19 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 72 (Polychromatic418967fa.accept_16_13_3_8_1_2422 13 19 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 72
  (Polychromatic418967fa.accept_13_12_6_7_1_1071 12 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 72 (accept_3_5 11 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 19
  72 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 19 72 (Polychromatic418967fa.accept_13_9_6_7_1_551 9 19 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 72 (accept_3_5 8 19 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 19 72 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 19 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 72 (Polychromatic418967fa.accept_17_6_2_4_1_2421 6
  19 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 19 72 (accept_3_5 5 19 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19 72 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 19
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 19 72
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 19 72 (accept_3_5 2 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 72
  (Polychromatic418967fa.accept_10_1_9_2_1_45 1 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 19 72))))))))))))))))))) (allB_succ 18 72 (allA_succ_of_accept 17 18 72
  (Polychromatic418967fa.accept_15_2_3_12_1_891 17 18 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 18 72 2 8 9 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 18 72 3 5 6 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 18 72 2 7 9 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 72 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 18 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 72 6 2 3 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 72 (Polychromatic418967fa.accept_13_11_5_7_1_2420 11 18 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 18 72 2 5 9 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 18 72 9 1 2 8 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 18 72 2 4 9 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 72
  (Polychromatic418967fa.accept_15_7_3_12_1_365 7 18 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 18 72 6 1 3 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 18 72 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 18 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 72 2 2 9 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 18 72 3 1 6 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 18 72 2 1 9 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 72 (Polychromatic418967fa.accept_11_1_7_6_1_378 1 18 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 72)))))))))))))))))) (allB_succ 17 72
  (allA_succ_of_accept 16 17 72 (accept_3_4 16 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17
  72 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 17 72 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 17 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 72 (accept_3_4 13 17 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 17 72 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 17 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 72 (Polychromatic418967fa.accept_13_11_4_7_1_2419
  11 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 72 (accept_3_4 10 17
  72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 72 (Polychromatic418967fa.accept_10_9_7_2_1_887
  9 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 72
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 72 (accept_3_4 7 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 72
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 72 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 17 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 72 (accept_3_4 4 17 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 72 (Polychromatic418967fa.accept_13_3_4_7_1_1711 3 17 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 72 (Polychromatic418967fa.accept_19_2_17_15_1_1377
  2 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 72 (accept_3_4 1 17 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 72))))))))))))))))) (allB_succ 16 72 (allA_succ_of_accept 15 16
  72 (Polychromatic418967fa.accept_17_15_16_4_1_2418 15 16 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 16 72 2 7 8 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 16 72 (Polychromatic418967fa.accept_15_13_1_12_1_1638 13 16 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 72 4 3 4 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 72 (accept_3_5 11 16 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 16 72 2 5 8 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 16 72 (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 16 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 72 8 1 2 9 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 72
  (Polychromatic418967fa.accept_21_7_16_9_1_2417 7 16 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 16 72 2 3 8 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 16 72 (accept_3_5 5 16 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 72 4
  1 4 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 72
  (Polychromatic418967fa.accept_17_3_16_4_1_2416 3 16 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 72 2 1 8 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 72 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 16 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 72)))))))))))))))) (allB_succ 15 72 (allA_succ_of_accept 14 15 72
  (Polychromatic418967fa.accept_21_14_15_9_1_1339 14 15 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 72 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 15 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 72 3 4 5 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 72 (Polychromatic418967fa.accept_17_11_15_4_1_2415 11 15 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 72
  (Polychromatic418967fa.accept_7_3_1_2_1_247 10 15 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 15 72 3 3 5 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 15 72 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 15 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 72 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 15 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 72 3 2 5 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 15 72
  (Polychromatic418967fa.accept_13_5_2_7_1_2414 5 15 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 15 72 (Polychromatic418967fa.accept_16_4_15_8_1_2413 4 15 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 72 3 1 5 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 72 (Polychromatic418967fa.accept_11_2_4_6_1_2412 2 15 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 72
  (Polychromatic418967fa.accept_16_1_15_8_1_2411 1 15 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 15 72))))))))))))))) (allB_succ 14 72 (allA_succ_of_accept 13 14 72 (accept_3_4 13 14 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 72 2 6 7 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 14 72 (Polychromatic418967fa.accept_13_11_1_7_1_1691 11 14 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 14 72 2 5 7 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 14 72
  (Polychromatic418967fa.accept_11_9_3_6_1_797 9 14 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 14 72 2 4 7 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 14 72 (accept_3_4 7 14 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 14 72 2
  3 7 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 14 72
  (Polychromatic418967fa.accept_21_5_14_9_1_2410 5 14 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 14 72 2 2 7 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 14 72 (Polychromatic418967fa.accept_13_3_1_7_1_1706 3 14 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 72 2 1 7 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 72 (accept_3_4 1 14 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 72)))))))))))))) (allB_succ 13 72 (allA_succ_of_accept 12 13 72
  (Polychromatic418967fa.accept_16_12_13_8_1_2409 12 13 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 72 (accept_3_5 11 13 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 13
  72 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 13 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 13 72 (Polychromatic418967fa.accept_17_9_13_4_1_2408 9 13 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 72 (accept_3_5 8 13 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 13 72 (Polychromatic418967fa.accept_19_7_13_15_1_2407 7 13 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 72 (Polychromatic418967fa.accept_19_6_13_15_1_2406
  6 13 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 13 72 (accept_3_5 5 13 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13 72 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 13
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 13 72
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 13 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 13 72 (accept_3_5 2 13 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 72
  (Polychromatic418967fa.accept_7_1_6_2_1_18 1 13 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 13 72))))))))))))) (allB_succ 12 72 (allA_succ_of_accept 11 12 72
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 12 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 12 72 2 5 6 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 12 72 3 3 4 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 12 72 4 2 3 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 12 72 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 12 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 72 6 1 2 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 72 (Polychromatic418967fa.accept_11_5_1_6_1_774 5 12 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 72 4 1 3 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 12 72 3 1 4 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 12 72 2 1 6 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 72
  (Polychromatic418967fa.accept_16_1_12_8_1_2405 1 12 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 72)))))))))))) (allB_succ 11 72 (allA_succ_of_accept 10 11 72 (accept_3_4 10 11 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 72 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 11 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 72
  (Polychromatic418967fa.accept_15_8_11_12_1_1626 8 11 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 11 72 (accept_3_4 7 11 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11 72
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 11 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 11 72 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 11 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 72 (accept_3_4 4 11 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 11 72 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 11 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 72 (Polychromatic418967fa.accept_19_2_11_15_1_2404
  2 11 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 72 (accept_3_4 1 11 72
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 72))))))))))) (allB_succ 10 72 (allA_succ_of_accept 9 10 72
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 9 10 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 10 72 2 4 5 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 10 72 (Polychromatic418967fa.accept_15_7_10_12_1_2403 7 10 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 10 72 2 3 5 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 10 72 (accept_3_5 5 10 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 10 72 2 2 5 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 10 72 (Polychromatic418967fa.accept_13_3_10_7_1_1061 3 10 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 10 72 2 1 5 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 10 72 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 10
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 72)))))))))) (allB_succ 9 72
  (allA_succ_of_accept 8 9 72 (Polychromatic418967fa.accept_13_8_9_7_1_530 8 9 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 72 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 9 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 72 3 2 3 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 72
  (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 9 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 9 72 (Polychromatic418967fa.accept_13_4_9_7_1_2402 4 9 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 9 72 3 1 3 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 9 72 (Polychromatic418967fa.accept_13_2_9_7_1_164 2 9 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 72
  (Polychromatic418967fa.accept_10_1_9_2_1_45 1 9 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 9 72))))))))) (allB_succ 8 72 (allA_succ_of_accept 7 8 72 (accept_3_4 7 8 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 8 72 2 3 4 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 8 72 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 8 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 72 4 1 2 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 72 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 8 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 72 2 1 4 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 72 (accept_3_4 1 8 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 8 72)))))))) (allB_succ 7 72 (allA_succ_of_accept 6 7 72
  (Polychromatic418967fa.accept_15_6_7_12_1_869 6 7 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 72 (accept_3_5 5 7 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 72
  (Polychromatic418967fa.accept_10_4_7_2_1_211 4 7 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 72 (Polychromatic418967fa.accept_15_3_7_12_1_372 3 7 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 72 (accept_3_5 2 7 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 72 (Polychromatic418967fa.accept_11_1_7_6_1_378 1 7 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 72))))))) (allB_succ 6 72 (allA_succ_of_accept 5 6 72
  (Polychromatic418967fa.accept_15_5_6_12_1_916 5 6 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 6 72 2 2 3 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 6 72 3 1 2 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 6 72 2 1 3 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 72 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 6 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 6 72)))))) (allB_succ 5 72 (allA_succ_of_accept 4 5 72 (accept_3_4 4 5 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 72 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 5 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 72
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 2 5 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 72 (accept_3_4 1 5 72 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 72))))) (allB_succ
  4 72 (allA_succ_of_accept 3 4 72 (Polychromatic418967fa.accept_13_3_4_7_1_1711 3 4 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 72 2 1 2 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 72 (Polychromatic418967fa.accept_15_1_4_12_1_2401 1 4 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 4 72)))) (allB_succ 3 72 (allA_succ_of_accept 2
  3 72 (Polychromatic418967fa.accept_15_2_3_12_1_891 2 3 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 72 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 3 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 3 72))) (allB_succ 2 72 (allA_succ_of_accept 1 2 72 (accept_3_4 1 2 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 2 72)) (allB_two
  72))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


