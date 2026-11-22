-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch150_Segment000
-- name    : Polychromatic418967fa_Branch150_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:27:18.471859+00:00
-- url     : https://prove2.me/theorems/6ad9801f-c957-4453-83b7-f4ed5f1dc57c
-- title:
--   Polychromatic branch proof segment
-- statement:
--   Checked segment of the pinned Polychromatic branch proof. Kernel types, definition values and allowed axioms match the original proof.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_150_segment_000 : allB 117 150 :=
  allB_succ' 35 116 150 (Eq.refl Bool.true) (allA_succ_of_gcd 34 116 150 2 17 58 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 150
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 116 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 116 150 2 16 58 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 116 150 (accept_3_4 31 116 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 116 150 2 15 58 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 116 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 116 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 116 150 2 14 58 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 116 150
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 116 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 116 150 2 13 58 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 116 150 (accept_3_4 25 116 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 116 150 2 12 58 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 116 150 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 116 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 150 2 11 58 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 150
  (Polychromatic418967fa.accept_9_3_8_6_1_80 21 116 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 116 150 2 10 58 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 116 150 (accept_3_4 19 116 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 116 150 2 9 58 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 116 150 (Polychromatic418967fa.accept_13_4_12_7_1_2439 17 116 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 116 150 2 8 58 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 116 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 15
  116 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 116 150 2 7 58 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 116 150 (accept_3_4 13
  116 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 116 150 2 6 58 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 116 150
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 116 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 116 150 2 5 58 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 116 150 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 116 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 116 150 2 4 58 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 116 150 (accept_3_4 7 116 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 116 150 2 3 58 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 116 150 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 116 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 116 150 2 2 58 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 116 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 3
  116 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 116 150 2 1 58 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 116 150 (accept_3_4 1
  116 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116 150))))))))))))))))))))))))))))))))))) (allB_succ' 36
  115 150 (Eq.refl Bool.true) (allA_succ_of_gcd 35 115 150 5 7 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 115 150 (Polychromatic418967fa.accept_14_6_3_10_1_3905 34 115
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 115 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 115 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 115 150 (accept_3_5 32 115 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 115 150 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 115 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 115 150 5 6 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 115 150 (accept_3_5 29 115 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 115 150 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 115 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 150 (Polychromatic418967fa.accept_13_1_11_7_1_1704 27 115
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 150 (accept_3_5 26 115
  150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 115 150 5 5 23 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 115 150
  (Polychromatic418967fa.accept_20_4_15_10_1_6519 24 115 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 115 150 (accept_3_5 23 115 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 115 150 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 115 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 115 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 115 150 5 4 23 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 115 150
  (Polychromatic418967fa.accept_9_1_7_6_1_75 19 115 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 115 150 (Polychromatic418967fa.accept_13_5_11_7_1_559 18 115 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 150 (accept_3_5 17 115 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 115 150 (Polychromatic418967fa.accept_13_3_11_7_1_2488 16 115 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 115 150 5 3 23 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 115 150 (accept_3_5 14 115 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 13
  115 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 150
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 115 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 150 (accept_3_5 11 115 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  115 150 5 2 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 115 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 115 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 115 150 (accept_3_5 8 115 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 115 150 (Polychromatic418967fa.accept_14_7_3_10_1_1364 7 115 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 150 (Polychromatic418967fa.accept_14_6_3_10_1_3905 6 115
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 115 150 5 1 23 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 115 150
  (Polychromatic418967fa.accept_9_4_7_6_1_255 4 115 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 115 150 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 115 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 150 (accept_3_5 2 115 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 115 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 115 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115 150)))))))))))))))))))))))))))))))))))) (allB_succ' 37 114 150
  (Eq.refl Bool.true) (allA_succ_of_gcd 36 114 150 6 6 19 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 114 150 (Polychromatic418967fa.accept_16_3_2_6_1_4461 35 114 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 150 2 17 57 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 114 150 3 11 38 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 114 150 2 16 57 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 114 150
  (Polychromatic418967fa.accept_20_11_14_10_1_2320 31 114 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 114 150 6 5 19 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 114 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 114 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 150 2 14 57 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 114 150 3 9 38 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 114 150 2 13 57 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 150
  (Polychromatic418967fa.accept_11_3_4_7_1_114 25 114 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 150 6 4 19 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 114 150 (Polychromatic418967fa.accept_21_2_9_3_1_4841 23 114 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 150 2 11 57 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 114 150 3 7 38 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 114 150 2 10 57 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 150
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 114 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 150 6 3 19 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 150 (Polychromatic418967fa.accept_13_4_10_7_1_1701 17 114 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 150 2 8 57 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 114 150 3 5 38 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 114 150 2 7 57 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 13
  114 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 150 6 2 19 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 150
  (Polychromatic418967fa.accept_16_11_2_6_1_1435 11 114 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 114 150 2 5 57 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 114 150 3 3 38 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 114 150 2 4 57 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 114 150 (Polychromatic418967fa.accept_21_7_9_3_1_8059 7 114 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 150 6 1 19 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 150 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 114 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 114 150 2 2 57 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 114 150 3 1 38 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 114 150 2 1 57 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 150
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 114 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 114 150))))))))))))))))))))))))))))))))))))) (allB_succ' 38 113 150 (Eq.refl Bool.true) (allA_succ_of_accept
  37 113 150 (accept_3_4 37 113 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 113 150
  (Polychromatic418967fa.accept_21_15_8_3_1_8086 36 113 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 113 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 113 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 150 (accept_3_4 34 113 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 113 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 113 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 150 (Polychromatic418967fa.accept_7_4_1_3_1_277
  32 113 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 113 150 (accept_3_4 31
  113 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 113 150
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 113 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 113 150 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 113 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 150 (accept_3_4 28 113 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 113 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 113 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 150 (Polychromatic418967fa.accept_7_5_1_3_1_103
  26 113 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 150 (accept_3_4 25
  113 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 113 150
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 24 113 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 113 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 113 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 150 (accept_3_4 22 113 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 113 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 113 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 150 (Polychromatic418967fa.accept_9_2_5_6_1_536
  20 113 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 150 (accept_3_4 19
  113 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 150
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 113 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 113 150 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 113 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 150 (accept_3_4 16 113 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 113 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 113 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 150
  (Polychromatic418967fa.accept_21_14_8_3_1_8085 14 113 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 150 (accept_3_4 13 113 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 113 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 113 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 150 (accept_3_4 10 113 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 150 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 113 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 150
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 113 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 150 (accept_3_4 7 113 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 150 (Polychromatic418967fa.accept_13_6_9_7_1_2430 6 113 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 113 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 150 (accept_3_4 4 113 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 113 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 150
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 113 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 150 (accept_3_4 1 113 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  150)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 112 150 (Eq.refl Bool.true) (allA_succ_of_gcd 38 112 150 2 19
  56 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 112 150
  (Polychromatic418967fa.accept_9_1_4_6_1_5 37 112 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 112 150 2 18 56 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 112 150 (accept_3_5 35 112 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 112 150 2 17 56 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 112 150 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 112 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 112 150 2 16 56 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 112 150
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 31 112 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 112 150 2 15 56 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 112 150 (accept_3_5 29 112 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 112 150 2 14 56 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 112 150 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 112 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 112 150 2 13 56 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 112 150
  (Polychromatic418967fa.accept_9_7_4_6_1_273 25 112 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 112 150 2 12 56 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 112 150 (accept_3_5 23 112 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 112 150 2 11 56 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 112 150 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 112 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 112 150 2 10 56 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 112 150
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 112 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 112 150 2 9 56 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 112 150 (accept_3_5 17 112 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  112 150 2 8 56 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 112 150 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 112 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 112 150 2 7 56 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 112 150 (Polychromatic418967fa.accept_17_13_10_14_1_4211 13 112 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 112 150 2 6 56 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 112 150 (accept_3_5 11
  112 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 112 150 2 5 56 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 112 150
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 112 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 112 150 2 4 56 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 112 150 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 112 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 112 150 2 3 56 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 112 150 (accept_3_5 5 112 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 112 150 2 2 56 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 112 150 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 112 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 112 150 2 1 56 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 112 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 112
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  150))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 111 150 (Eq.refl Bool.true) (allA_succ_of_gcd 39 111 150 3
  13 37 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 111
  150 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 111 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 111 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 111 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 111 150 3 12 37 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 111 150 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  111 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 150
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 111 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 111 150 3 11 37 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 111 150 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 111 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 150 (Polychromatic418967fa.accept_9_4_3_6_1_532
  31 111 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 111 150 3 10 37 50
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 111 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 111 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 150 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 111 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 111 150 3 9 37 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 111 150 (Polychromatic418967fa.accept_9_8_3_6_1_533 26
  111 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 111 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 111 150 3 8 37 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 111 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 111 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 150 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 111 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 111 150 3 7 37 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 111 150
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 111 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 111 150 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 111 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 111 150 3 6 37 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 111 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  111 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 150
  (Polychromatic418967fa.accept_7_2_6_3_1_100 16 111 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 111 150 3 5 37 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 111 150 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 111 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 111 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 111 150 3 4 37 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 111 150
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 111 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 150 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 111 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 111 150 3 3 37 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 111 150 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 111 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 150
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 111 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 111 150 3 2 37 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 111 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 111 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 150 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 111 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 111 150 3 1 37 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 111 150
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 111 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 111 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 111 150)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 110 150
  (Eq.refl Bool.true) (allA_succ_of_gcd 40 110 150 10 4 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 110 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 110 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 110 150 2 19 55 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 110 150 (accept_3_4 37
  110 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 110 150 2 18 55 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 110 150 5 7 22 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 110 150 2 17 55 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 110 150
  (Polychromatic418967fa.accept_12_9_2_6_1_455 33 110 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 110 150 2 16 55 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 110 150 (accept_3_4 31 110 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 110 150 10 3 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 110 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 110 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 150 2 14 55 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 150
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 110 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 110 150 2 13 55 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 110 150 5 5 22 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 110 150 2 12 55 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 110 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 110 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 150 2 11 55 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 150
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 110 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 150 10 2 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 150 (accept_3_4 19 110 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 150 2 9 55 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 110 150 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 110 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 150 2 8 55 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 110 150 5 3 22 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 110 150 2 7 55 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 110 150 (accept_3_4 13 110 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 110 150 2 6 55 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 110 150 (Polychromatic418967fa.accept_17_11_8_14_1_8084 11 110
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 110 150 10 1 11 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 110 150
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 110 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 110 150 2 4 55 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 110 150 (accept_3_4 7 110 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 110
  150 2 3 55 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 110
  150 5 1 22 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 110
  150 2 2 55 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  110 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 110 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 110 150 2 1 55 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 110 150 (accept_3_4 1 110 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  150))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 109 150 (Eq.refl Bool.true) (allA_succ_of_accept 41 109
  150 (accept_3_5 41 109 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 150
  (Polychromatic418967fa.accept_9_4_1_6_1_284 40 109 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 109 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 109 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 109 150 (accept_3_5 38 109 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 109 150 (Polychromatic418967fa.accept_13_11_5_7_1_2420 37 109 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 109 150
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 109 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 109 150 (accept_3_5 35 109 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 109 150 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 109 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 109 150 (Polychromatic418967fa.accept_20_13_9_10_1_8083 33 109 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 109 150 (accept_3_5 32 109 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 109 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 109 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 109 150
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 109 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 109 150 (accept_3_5 29 109 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 109 150 (Polychromatic418967fa.accept_13_2_5_7_1_1695 28 109 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 109 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 109 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 109 150 (accept_3_5 26 109 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 109 150 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 109 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 109 150
  (Polychromatic418967fa.accept_13_11_5_7_1_2420 24 109 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 109 150 (accept_3_5 23 109 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 109 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 109 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 109 150 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 109 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 150 (accept_3_5 20 109 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 109 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 109 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 109 150
  (Polychromatic418967fa.accept_21_18_4_3_1_8082 18 109 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 109 150 (accept_3_5 17 109 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 109 150 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 109 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 109 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 109 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 150 (accept_3_5 14 109 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 150 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 109 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 150
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 109 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 109 150 (accept_3_5 11 109 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 109 150 (Polychromatic418967fa.accept_17_10_7_14_1_4244 10 109 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 109 150 (Polychromatic418967fa.accept_16_9_13_6_1_2334 9 109 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 150 (accept_3_5 8 109 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 109 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 150
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 109 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 150 (accept_3_5 5 109 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 150 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 109 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 109 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 150 (accept_3_5 2 109 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 109 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109 150))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 43 108 150 (Eq.refl Bool.true) (allA_succ_of_gcd 42 108 150 6 7 18 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 108 150
  (Polychromatic418967fa.accept_17_7_6_14_1_6737 41 108 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 108 150 2 20 54 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 108 150 3 13 36 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 108 150 2 19 54 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 108 150 (Polychromatic418967fa.accept_13_11_4_7_1_2419 37 108
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 108 150 6 6 18 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 108 150
  (Polychromatic418967fa.accept_11_2_9_7_1_124 35 108 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 108 150 2 17 54 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 108 150 3 11 36 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 108 150 2 16 54 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 150 (Polychromatic418967fa.accept_22_9_20_18_1_8035 31 108
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 108 150 6 5 18 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 108 150
  (Polychromatic418967fa.accept_13_3_4_7_1_1711 29 108 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 108 150 2 14 54 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 108 150 3 9 36 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 108 150 2 13 54 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 108 150 (Polychromatic418967fa.accept_13_12_4_7_1_2520 25 108 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 108 150 6 4 18 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 108 150
  (Polychromatic418967fa.accept_13_10_4_7_1_2465 23 108 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 108 150 2 11 54 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 108 150 3 7 36 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 108 150 2 10 54 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 108 150 (Polychromatic418967fa.accept_13_6_4_7_1_2464 19 108 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 108 150 6 3 18 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 108 150
  (Polychromatic418967fa.accept_20_17_8_10_1_8081 17 108 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 108 150 2 8 54 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 15 108 150 3 5 36 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 108 150 2 7 54 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 108 150 (Polychromatic418967fa.accept_11_2_9_7_1_124 13 108 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 150 6 2 18 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 150
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 11 108 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 108 150 2 5 54 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 108 150 3 3 36 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 108 150 2 4 54 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 108 150 (Polychromatic418967fa.accept_17_7_6_14_1_6737 7 108 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 150 6 1 18 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 150 (Polychromatic418967fa.accept_11_5_9_7_1_411 5 108 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 150 2 2 54 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 108 150 3 1 36 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 108 150 2 1 54 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 150
  (Polychromatic418967fa.accept_22_1_20_18_1_8080 1 108 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 108 150))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 107 150 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 107 150 (accept_3_4 43 107 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 150 (Polychromatic418967fa.accept_24_18_11_6_1_8079 42 107 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 107 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 150 (accept_3_4 40 107 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 107 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 150
  (Polychromatic418967fa.accept_9_2_8_6_1_79 38 107 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 150 (accept_3_4 37 107 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 107 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 150 (Polychromatic418967fa.accept_13_9_3_7_1_1065 35 107 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 150 (accept_3_4 34 107 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 107 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 150
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 107 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 107 150 (accept_3_4 31 107 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 107 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 107 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 107 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 107 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 150 (accept_3_4 28 107 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 107 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 150
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 107 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 150 (accept_3_4 25 107 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 150 (Polychromatic418967fa.accept_13_11_3_7_1_2513 24 107 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 150 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 107 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 150 (accept_3_4 22 107 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 107 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 150
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 107 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 150 (accept_3_4 19 107 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 150 (Polychromatic418967fa.accept_16_2_11_6_1_737 18 107 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 107 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 150 (accept_3_4 16 107 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 107 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 150
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 107 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 150 (accept_3_4 13 107 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 150 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 107 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 150 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 107 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 150 (accept_3_4 10 107 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 107 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 150
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 107 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 150 (accept_3_4 7 107 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 107 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 107 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 150 (accept_3_4 4 107 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 107 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 150
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 107 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 150 (accept_3_4 1 107 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  150)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 106 150 (Eq.refl Bool.true) (allA_succ_of_gcd 44 106
  150 2 22 53 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43
  106 150 (Polychromatic418967fa.accept_17_9_4_14_1_4302 43 106 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 106 150 2 21 53 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 106 150 (accept_3_5 41 106 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 106 150 2 20 53 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 106 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 106 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 106 150 2 19 53 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 106 150
  (Polychromatic418967fa.accept_7_2_1_3_1_102 37 106 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 106 150 2 18 53 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 106 150 (accept_3_5 35 106 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 106 150 2 17 53 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 106 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 106 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 106 150 2 16 53 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 106 150
  (Polychromatic418967fa.accept_9_4_7_6_1_255 31 106 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 106 150 2 15 53 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 106 150 (accept_3_5 29 106 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 106 150 2 14 53 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 106 150 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 106 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 106 150 2 13 53 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 106 150
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 106 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 106 150 2 12 53 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 106 150 (accept_3_5 23 106 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 106 150 2 11 53 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 150 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 106 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 106 150 2 10 53 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 150
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 106 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 106 150 2 9 53 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 106 150 (accept_3_5 17 106 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  106 150 2 8 53 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 106 150 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 106 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 106 150 2 7 53 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 106 150 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 106 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 106 150 2 6 53 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 106 150 (accept_3_5 11 106 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 106 150 2 5 53 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 106 150
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 106 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 106 150 2 4 53 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 106 150 (Polychromatic418967fa.accept_17_7_4_14_1_2106 7 106 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 106 150 2 3 53 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 106 150 (accept_3_5 5 106 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 106 150 2 2 53 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 106 150 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 106 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 106 150 2 1 53 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 106 150 (Polychromatic418967fa.accept_9_1_7_6_1_75 1
  106 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  150))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 105 150 (Eq.refl Bool.true) (allA_succ_of_gcd 45 105
  150 15 3 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  105 150 (Polychromatic418967fa.accept_12_8_9_6_1_127 44 105 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 105 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 105 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 105 150 3 14 35 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 105 150
  (Polychromatic418967fa.accept_18_5_15_6_1_3999 41 105 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 105 150 5 8 21 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 105 150 3 13 35 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 105 150 (Polychromatic418967fa.accept_12_2_9_6_1_439 38 105 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 150
  (Polychromatic418967fa.accept_13_11_1_7_1_1691 37 105 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 105 150 3 12 35 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 105 150 5 7 21 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 105 150 (Polychromatic418967fa.accept_11_1_6_7_1_116 34 105 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 105 150 3 11 35 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 105 150
  (Polychromatic418967fa.accept_12_8_9_6_1_127 32 105 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 105 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 105 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 105 150 15 2 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 105 150 (Polychromatic418967fa.accept_13_3_1_7_1_1706
  29 105 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 150
  (Polychromatic418967fa.accept_12_4_9_6_1_440 28 105 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 105 150 3 9 35 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 105 150 (Polychromatic418967fa.accept_12_2_9_6_1_439 26 105 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 105 150 5 5 21 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 105 150 3 8 35 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 105 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 23
  105 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 150
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 105 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 105 150 3 7 35 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 105 150 5 4 21 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 105 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 105 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 105 150 3 6 35 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 105 150 (Polychromatic418967fa.accept_14_3_7_10_1_2146
  17 105 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 150
  (Polychromatic418967fa.accept_12_4_9_6_1_440 16 105 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 105 150 15 1 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 105 150 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 105 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 150 (Polychromatic418967fa.accept_16_13_9_6_1_2306 13 105
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 105 150 3 4 35 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 105 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 105 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 105 150 5 2 21 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 105 150 3 3 35 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 105 150 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 105 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 105 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 105 150 3 2 35 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 105 150 5 1 21 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 105 150
  (Polychromatic418967fa.accept_12_4_9_6_1_440 4 105 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 105 150 3 1 35 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 105 150 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 105 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 150 (Polychromatic418967fa.accept_11_1_6_7_1_116 1 105 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  150)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 104 150 (Eq.refl Bool.true) (allA_succ_of_gcd 46 104
  150 2 23 52 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  104 150 (Polychromatic418967fa.accept_12_9_8_6_1_466 45 104 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 104 150 2 22 52 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 104 150 (accept_3_4 43 104 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 104 150 2 21 52 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 104 150 (Polychromatic418967fa.accept_20_1_4_10_1_3645 41 104 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 104 150 2 20 52 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 104 150
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 104 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 104 150 2 19 52 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 104 150 (accept_3_4 37 104 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 104 150 2 18 52 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 104 150 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 104 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 104 150 2 17 52 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 104 150
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 104 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 104 150 2 16 52 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 104 150 (accept_3_4 31 104 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 104 150 2 15 52 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 104 150 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 104 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 104 150 2 14 52 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 104 150
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 104 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 104 150 2 13 52 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 104 150 (accept_3_4 25 104 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 104 150 2 12 52 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 104 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 104 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 150 2 11 52 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 150
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 104 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 104 150 2 10 52 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 104 150 (accept_3_4 19 104 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 104 150 2 9 52 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 104 150 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 104 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 104 150 2 8 52 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 104 150 (Polychromatic418967fa.accept_12_3_8_6_1_895
  15 104 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 150 2 7 52 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 104 150
  (accept_3_4 13 104 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 104 150 2 6 52 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 150
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 104 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 104 150 2 5 52 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 104 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 104 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 104 150 2 4 52 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 104 150 (accept_3_4 7 104 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 104 150 2 3 52 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 104 150 (Polychromatic418967fa.accept_17_5_2_14_1_4270 5 104 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 104 150 2 2 52 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 104 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 3
  104 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 150 2 1 52 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 150 (accept_3_4 1
  104 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104 150)))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 48 103 150 (Eq.refl Bool.true) (allA_succ_of_accept 47 103 150 (accept_3_5 47 103 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 103 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 103 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 103 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 103 150 (accept_3_5 44 103 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 103 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 103 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 103 150 (Polychromatic418967fa.accept_19_4_8_17_1_8054 42 103 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 150 (accept_3_5 41 103 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 150 (Polychromatic418967fa.accept_14_12_5_10_1_2130 40 103
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 150
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 103 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 150 (accept_3_5 38 103 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 103 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 103 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 150 (accept_3_5 35 103 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 150 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 103 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 103 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 150 (accept_3_5 32 103 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 150 (Polychromatic418967fa.accept_13_5_12_7_1_1080 31 103 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 103 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 150 (accept_3_5 29 103 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 103 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 150
  (Polychromatic418967fa.accept_17_10_1_14_1_489 27 103 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 150 (accept_3_5 26 103 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 103 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 150 (Polychromatic418967fa.accept_13_11_12_7_1_2443 24 103 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 150 (accept_3_5 23 103 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 103 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 103 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 150 (accept_3_5 20 103 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 103 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 150 (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 103 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 150 (accept_3_5 17 103 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 103 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 150
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 103 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 150 (accept_3_5 14 103 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 103 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 150 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 103 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 150 (accept_3_5 11 103 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 103 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 103 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 150 (accept_3_5 8 103 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 150 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 103 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 150 (Polychromatic418967fa.accept_13_6_12_7_1_5131 6 103 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 150 (accept_3_5 5 103 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 150 (Polychromatic418967fa.accept_13_4_12_7_1_2439 4 103
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 150
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 103 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 150 (accept_3_5 2 103 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 103 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103 150)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 102 150 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 102 150 6 8 17 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 150 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 102 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 102 150 2 23 51 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 102 150 3 15 34 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 102 150 2 22 51 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 102 150
  (Polychromatic418967fa.accept_7_1_4_3_1_21 43 102 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 150 6 7 17 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 102 150 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 102 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 150 2 20 51 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 102 150 3 13 34 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 102 150 2 19 51 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 102 150
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 102 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 150 6 6 17 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 102 150 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 102 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 150 2 17 51 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 102 150 3 11 34 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 102 150 2 16 51 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 150
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 102 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 150 6 5 17 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 102 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 102 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 150 2 14 51 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 102 150 3 9 34 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 102 150 2 13 51 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 150
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 102 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 150 6 4 17 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 102 150 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 102 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 150 2 11 51 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 102 150 3 7 34 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 102 150 2 10 51 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 150
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 102 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 150 6 3 17 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 150 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 102 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 150 2 8 51 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 102 150 3 5 34 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 102 150 2 7 51 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 150 (Polychromatic418967fa.accept_7_6_4_3_1_266 13
  102 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 150 6 2 17 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 150
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 102 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 102 150 2 5 51 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 102 150 3 3 34 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 102 150 2 4 51 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 150 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 102 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 150 6 1 17 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 150 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 102 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102 150 2 2 51 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 102 150 3 1 34 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 102 150 2 1 51 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 150
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 102 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 102 150))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 101 150 (Eq.refl Bool.true)
  (allA_succ_of_accept 49 101 150 (accept_3_4 49 101 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 101 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 101 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 101 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 101 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 150 (accept_3_4 46 101 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 150 (Polychromatic418967fa.accept_17_11_16_14_1_6760 45 101 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 150
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 101 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 101 150 (accept_3_4 43 101 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 101 150 (Polychromatic418967fa.accept_11_9_2_7_1_1298 42 101 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 101 150 (Polychromatic418967fa.accept_9_5_2_6_1_265 41 101 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 150 (accept_3_4 40 101 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 101 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 150
  (Polychromatic418967fa.accept_13_12_10_7_1_2433 38 101 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 101 150 (accept_3_4 37 101 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 101 150 (Polychromatic418967fa.accept_16_4_5_6_1_8071 36 101 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 101 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 150 (accept_3_4 34 101 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 150 (Polychromatic418967fa.accept_16_1_5_6_1_4435
  33 101 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 150
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 101 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 150 (accept_3_4 31 101 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 101 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 150 (Polychromatic418967fa.accept_13_3_10_7_1_1061 29 101 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 150 (accept_3_4 28 101 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 101 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 150
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 101 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 150 (accept_3_4 25 101 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 150 (Polychromatic418967fa.accept_20_4_1_10_1_3643 24 101 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 101 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 150 (accept_3_4 22 101 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 101 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 150
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 20 101 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 150 (accept_3_4 19 101 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 150 (Polychromatic418967fa.accept_19_18_6_17_1_8078 18 101 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 150 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 101 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 150 (accept_3_4 16 101 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 101 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 150
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 101 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 150 (accept_3_4 13 101 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 101 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 101 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 150 (accept_3_4 10 101 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 150 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 101 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 150
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 101 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 150 (accept_3_4 7 101 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 150 (Polychromatic418967fa.accept_14_6_3_10_1_3905 6 101 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 150 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 101 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 150 (accept_3_4 4 101 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 101 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 150
  (Polychromatic418967fa.accept_17_2_16_14_1_2116 2 101 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 150 (accept_3_4 1 101 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  150)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 100 150 (Eq.refl Bool.true) (allA_succ_of_gcd 50
  100 150 50 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  49 100 150 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 100 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 100 150 2 24 50 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 100 150 (accept_3_5 47 100 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 100 150 2 23 50 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 100 150 5 9 20 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 100 150 2 22 50 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 100 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 100 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 100 150 2 21 50 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 100 150 (accept_3_5 41 100 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 100 150 10 4 10 15 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 100 150
  (Polychromatic418967fa.accept_9_3_1_6_1_86 39 100 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 100 150 2 19 50 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 100 150 (Polychromatic418967fa.accept_13_11_9_7_1_2484 37 100 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 100 150 2 18 50 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 100 150 5 7 20 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 100 150 2 17 50 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 100 150
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 100 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 100 150 2 16 50 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 100 150 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 100 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 100 150 10 3 10 15 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 100 150 (accept_3_5 29 100 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 100 150 2 14 50 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 100 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 27
  100 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 100 150 2 13 50 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 100 150 25 1 4 6 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 100 150 2 12 50 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 100 150
  (accept_3_5 23 100 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 100 150 2 11 50 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 100 150
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 100 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 100 150 10 2 10 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 100 150 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 100 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 100 150 2 9 50 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 100 150 (accept_3_5 17 100 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 100 150 2 8 50 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 100 150 5 3 20 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 100 150 2 7 50 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 100 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 13
  100 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 100 150 2 6 50 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 100 150 (accept_3_5 11
  100 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 100 150 10 1 10 15 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 100 150
  (Polychromatic418967fa.accept_12_9_4_6_1_460 9 100 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 100 150 2 4 50 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 100 150 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 100 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 100 150 2 3 50 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 100 150 5 1 20 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 100 150 2 2 50 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 100 150 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 100 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 100 150 2 1 50 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 100 150
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 100 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 100 150))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 99 150 (Eq.refl Bool.true)
  (allA_succ_of_gcd 51 99 150 3 17 33 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 99 150 (Polychromatic418967fa.accept_12_2_3_6_1_112 50 99 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 99 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 99 150 3 16 33 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 99 150
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 99 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 99 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 99 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 99 150 3 15 33 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 99 150 (Polychromatic418967fa.accept_7_2_1_3_1_102 44
  99 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 150
  (Polychromatic418967fa.accept_16_11_3_6_1_4462 43 99 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 99 150 3 14 33 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 99 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 99 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 99 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 99 150 3 13 33 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 99 150
  (Polychromatic418967fa.accept_12_2_3_6_1_112 38 99 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 99 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 99 150 3 12 33 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 99 150 (Polychromatic418967fa.accept_13_9_8_7_1_1073
  35 99 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 150
  (Polychromatic418967fa.accept_12_10_3_6_1_882 34 99 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 99 150 3 11 33 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 99 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 99 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 150 (Polychromatic418967fa.accept_18_13_9_6_1_4024 31 99
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 99 150 3 10 33 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 99 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 99 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 150 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 99 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 99 150 3 9 33 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 99 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 99 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 99 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 99 150 3 8 33 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 99 150 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 99 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 150 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 99 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 99 150 3 7 33 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 99 150
  (Polychromatic418967fa.accept_12_8_3_6_1_909 20 99 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 99 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 99 150 3 6 33 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 99 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 99 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 150
  (Polychromatic418967fa.accept_7_2_1_3_1_102 16 99 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 99 150 3 5 33 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 99 150 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 99 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 99 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 99 150 3 4 33 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 99 150
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 99 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 150 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 99 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 99 150 3 3 33 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 99 150 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 99 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 150
  (Polychromatic418967fa.accept_18_7_9_6_1_4023 7 99 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 99 150 3 2 33 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 99 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 99 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 99 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 99 150 3 1 33 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 99 150
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 99 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 99 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 99 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 99 150)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 98
  150 (Eq.refl Bool.true) (allA_succ_of_gcd 52 98 150 2 26 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 98 150 (Polychromatic418967fa.accept_12_3_2_6_1_138 51 98 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 98 150 2 25 49 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 98 150 (accept_3_4 49
  98 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 98 150 2 24 49 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 98 150
  (Polychromatic418967fa.accept_9_2_8_6_1_79 47 98 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 98 150 2 23 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 98 150 (Polychromatic418967fa.accept_12_9_2_6_1_455 45 98 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 98 150 2 22 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 98 150 (accept_3_4 43 98 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 98 150 2 21 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 98 150 (Polychromatic418967fa.accept_9_5_8_6_1_281 41 98 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 98 150 2 20 49 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 98 150
  (Polychromatic418967fa.accept_9_3_8_6_1_80 39 98 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 98 150 2 19 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 98 150 (accept_3_4 37 98 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 98
  150 2 18 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  98 150 (Polychromatic418967fa.accept_16_3_2_6_1_4461 35 98 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 98 150 2 17 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 98 150 (Polychromatic418967fa.accept_12_9_2_6_1_455 33 98 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 98 150 2 16 49 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 98 150 (accept_3_4 31 98 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 98 150 2 15 49 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 98 150
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 98 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 98 150 2 14 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 98 150 (Polychromatic418967fa.accept_12_3_2_6_1_138 27 98 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 98 150 2 13 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 98 150 (accept_3_4 25 98 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 98 150 2 12 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 98 150 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 98 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 98 150 2 11 49 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 98 150
  (Polychromatic418967fa.accept_9_3_8_6_1_80 21 98 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 98 150 2 10 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 98 150 (accept_3_4 19 98 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 98
  150 2 9 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  98 150 (Polychromatic418967fa.accept_16_1_2_6_1_2295 17 98 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 98 150 2 8 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 98 150 (Polychromatic418967fa.accept_12_3_2_6_1_138 15 98 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 98 150 2 7 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 98 150 (accept_3_4 13 98 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98 150 2 6 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 98 150 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 98 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 98 150 2 5 49 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 98 150
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 98 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 98 150 2 4 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 98 150 (accept_3_4 7 98 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 98 150
  2 3 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 98
  150 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 98 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 98 150 2 2 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 98 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 98 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 98 150 2 1 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 98 150 (accept_3_4 1 98 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 98 150))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 97 150 (Eq.refl
  Bool.true) (allA_succ_of_accept 53 97 150 (accept_3_5 53 97 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 97 150 (Polychromatic418967fa.accept_19_14_2_17_1_678 52 97 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 97 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 97 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 150 (accept_3_5 50 97 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 150 (Polychromatic418967fa.accept_9_4_7_6_1_255 49
  97 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 150
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 97 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 150 (accept_3_5 47 97 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 150 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 97 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 150 (Polychromatic418967fa.accept_14_3_13_10_1_761 45 97 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 150 (accept_3_5 44 97 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 97 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 150
  (Polychromatic418967fa.accept_19_4_2_17_1_3870 42 97 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 150 (accept_3_5 41 97 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 150 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 97 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 97 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 150 (accept_3_5 38 97 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 97 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 150
  (Polychromatic418967fa.accept_24_12_1_6_1_8077 36 97 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 150 (accept_3_5 35 97 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 150 (Polychromatic418967fa.accept_16_2_1_6_1_2342 34 97 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 150 (Polychromatic418967fa.accept_19_14_2_17_1_678 33 97 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 150 (accept_3_5 32 97 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 97 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 150
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 97 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 150 (accept_3_5 29 97 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 150 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 97 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 97 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 150 (accept_3_5 26 97 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 150 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 97 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 150
  (Polychromatic418967fa.accept_11_2_9_7_1_124 24 97 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 150 (accept_3_5 23 97 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 150 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 97 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 150 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 97 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 150 (accept_3_5 20 97 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 97 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 150
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 97 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 150 (accept_3_5 17 97 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 97 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 97 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 150 (accept_3_5 14 97 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 150 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 97 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 150
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 97 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 150 (accept_3_5 11 97 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 150 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 97 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 97 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 150 (accept_3_5 8 97 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 97 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 150
  (Polychromatic418967fa.accept_21_6_13_3_1_4851 6 97 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 150 (accept_3_5 5 97 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  150 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 97 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 97 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 150 (accept_3_5 2 97 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 150 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 97 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97 150))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 55 96 150 (Eq.refl Bool.true) (allA_succ_of_gcd 54 96 150 6 9 16 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 150
  (Polychromatic418967fa.accept_19_15_1_17_1_670 53 96 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 96 150 2 26 48 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 51 96 150 3 17 32 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 96 150 2 25 48 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 96 150 (Polychromatic418967fa.accept_20_9_16_10_1_3559 49 96 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 150 6 8 16 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 150 (Polychromatic418967fa.accept_14_5_12_10_1_2985 47 96
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96 150 2 23 48 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 96 150 3 15 32 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 96 150 2 22 48 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 96 150
  (Polychromatic418967fa.accept_7_1_5_3_1_268 43 96 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 96 150 6 7 16 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 96 150 (Polychromatic418967fa.accept_13_2_5_7_1_1695 41 96 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 96 150 2 20 48 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 96 150 3 13 32 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 96 150 2 19 48 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 37
  96 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 150 6 6 16 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 150
  (Polychromatic418967fa.accept_19_16_1_17_1_8065 35 96 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 96 150 2 17 48 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 96 150 3 11 32 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 96 150 2 16 48 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 96 150 (Polychromatic418967fa.accept_21_10_12_3_1_8076 31 96 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 150 6 5 16 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 96 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96 150 2 14 48 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 96 150 3 9 32 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 96 150 2 13 48 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 150
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 25 96 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 150 6 4 16 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 96 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 96 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96 150 2 11 48 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 96 150 3 7 32 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 96 150 2 10 48 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 96 150 (Polychromatic418967fa.accept_14_5_12_10_1_2985
  19 96 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 150 6 3 16 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 150
  (Polychromatic418967fa.accept_21_17_12_3_1_4848 17 96 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 96 150 2 8 48 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 96 150 3 5 32 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 96 150 2 7 48 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 96 150 (Polychromatic418967fa.accept_21_13_12_3_1_8028 13 96 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 150 6 2 16 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 150 (Polychromatic418967fa.accept_13_11_5_7_1_2420 11 96 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 150 2 5 48 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 96 150 3 3 32 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 96 150 2 4 48 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 96 150
  (Polychromatic418967fa.accept_21_7_12_3_1_4849 7 96 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 96 150 6 1 16 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 96 150 (Polychromatic418967fa.accept_14_5_12_10_1_2985 5 96 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 150 2 2 48 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 96 150 3 1 32 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 96 150 2 1 48 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 96 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  150))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 95 150 (Eq.refl Bool.true) (allA_succ_of_gcd
  55 95 150 5 11 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 95 150 (Polychromatic418967fa.accept_20_14_15_10_1_3554 54 95 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 95 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 95 150 (accept_3_4 52 95 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 95 150 (Polychromatic418967fa.accept_13_12_4_7_1_2520
  51 95 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 95 150 5 10 19 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 95 150 (accept_3_4 49
  95 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 150
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 95 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 95 150 (Polychromatic418967fa.accept_9_2_5_6_1_536 47 95 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 95 150 (accept_3_4 46 95 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 95 150 5 9 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 95 150 (Polychromatic418967fa.accept_9_8_5_6_1_538 44 95 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 150 (accept_3_4 43 95 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 150 (Polychromatic418967fa.accept_13_3_4_7_1_1711 42 95 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 95 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 95 150 5 8 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 95 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 95 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 95 150 (Polychromatic418967fa.accept_9_2_5_6_1_536 38 95 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 150 (accept_3_4 37 95 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 36
  95 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 95 150 5 7 19 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 95 150 (accept_3_4 34
  95 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 95 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 95 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 95 150 (Polychromatic418967fa.accept_13_6_4_7_1_2464 32 95 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 150 (accept_3_4 31 95 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 95 150 5 6 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 95 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 95 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 95 150 (accept_3_4 28 95 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 95 150 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 95 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 150
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 95 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 95 150 5 5 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 95 150 (Polychromatic418967fa.accept_13_11_4_7_1_2419 24 95 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 150 (Polychromatic418967fa.accept_13_10_4_7_1_2465 23 95
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 150 (accept_3_4 22 95 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 95 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 21
  95 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 95 150 5 4 19 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 95 150 (accept_3_4 19
  95 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 150
  (Polychromatic418967fa.accept_17_1_10_14_1_1173 18 95 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 95 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 95 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 150 (accept_3_4 16 95 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 95 150 5 3 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 95 150 (Polychromatic418967fa.accept_20_14_15_10_1_3554 14 95 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 150 (accept_3_4 13 95 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 95 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 150
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 95 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 95 150 5 2 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 95 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 95 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 95 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 150 (accept_3_4 7 95 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 150 (Polychromatic418967fa.accept_7_6_4_3_1_266 6
  95 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 95 150 5 1 19 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 95 150 (accept_3_4 4 95
  150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95 150 (Polychromatic418967fa.accept_9_3_5_6_1_253
  3 95 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 150
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 95 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 95 150 (accept_3_4 1 95 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  150)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 94 150 (Eq.refl Bool.true)
  (allA_succ_of_gcd 56 94 150 2 28 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 94 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 94 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 94 150 2 27 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 94 150 (accept_3_5 53 94 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 94 150 2 26 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 94 150 (Polychromatic418967fa.accept_12_3_10_6_1_442 51 94 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 94 150 2 25 47 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 94 150
  (Polychromatic418967fa.accept_13_10_3_7_1_2517 49 94 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 94 150 2 24 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 94 150 (accept_3_5 47 94 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 94
  150 2 23 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  94 150 (Polychromatic418967fa.accept_11_1_6_7_1_116 45 94 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 94 150 2 22 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 94 150 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 94 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 94 150 2 21 47 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 94 150 (accept_3_5 41 94 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 94 150 2 20 47 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 94 150
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 94 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 94 150 2 19 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 94 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 94 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 94 150 2 18 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 94 150 (accept_3_5 35 94 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 94 150 2 17 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 94 150 (Polychromatic418967fa.accept_12_9_10_6_1_872 33 94 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 94 150 2 16 47 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 94 150
  (Polychromatic418967fa.accept_19_12_18_17_1_8075 31 94 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 94 150 2 15 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 94 150 (accept_3_5 29 94 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 94 150 2 14 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 94 150 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 94 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 94 150 2 13 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 94 150 (Polychromatic418967fa.accept_9_7_4_6_1_273 25
  94 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 94 150 2 12 47 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 94 150 (accept_3_5 23
  94 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 94 150 2 11 47 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 94 150
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 94 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 94 150 2 10 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 94 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 94 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 94 150 2 9 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 94 150 (accept_3_5 17 94 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 94 150 2 8 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 94 150 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 94 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 94 150 2 7 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 94 150
  (Polychromatic418967fa.accept_19_13_18_17_1_5141 13 94 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 94 150 2 6 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 94 150 (accept_3_5 11 94 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 94 150 2 5 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 94 150 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 94 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 94 150 2 4 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 94 150 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 94 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 94 150 2 3 47 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 94 150 (accept_3_5 5 94 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 94 150 2 2 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 94 150 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 94
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 94 150 2 1 47 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 150
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 94 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 94 150))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 93 150 (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 93 150 3 19 31 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 93 150 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 93 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 93 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 93 150 3 18 31 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 93 150
  (Polychromatic418967fa.accept_9_8_3_6_1_533 53 93 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 93 150 (Polychromatic418967fa.accept_9_7_3_6_1_270 52 93 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 93 150 3 17 31 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 93 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 50
  93 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 150
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 93 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 93 150 3 16 31 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 93 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 93 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 150 (Polychromatic418967fa.accept_9_1_3_6_1_70 46 93 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 93 150 3 15 31 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 93 150
  (Polychromatic418967fa.accept_9_8_3_6_1_533 44 93 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 93 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 93 150 3 14 31 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 93 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 41
  93 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 150
  (Polychromatic418967fa.accept_7_5_2_3_1_106 40 93 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 93 150 3 13 31 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 93 150 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 93 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 150 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 93 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 93 150 3 12 31 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 93 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 93 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 93 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 93 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 93 150 3 11 31 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 93 150 (Polychromatic418967fa.accept_9_5_3_6_1_269 32
  93 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 31 93 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 93 150 3 10 31 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 93 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 93 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 150 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 93 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 93 150 3 9 31 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 93 150
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 93 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 150 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 93 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 93 150 3 8 31 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 93 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 93 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 150
  (Polychromatic418967fa.accept_7_1_2_3_1_257 22 93 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 93 150 3 7 31 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 93 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 93 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 93 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 93 150 3 6 31 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 93 150
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 93 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 93 150 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 93 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 93 150 3 5 31 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 93 150 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 93 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 150
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 93 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 93 150 3 4 31 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 93 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 93 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 150 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 93 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 93 150 3 3 31 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 93 150
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 93 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 93 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 93 150 3 2 31 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 93 150 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 93 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 150
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 93 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 93 150 3 1 31 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 93 150 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 93 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 93 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  150)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 92 150 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 92 150 2 29 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 92 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 92 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 92 150 2 28 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 92 150 (accept_3_4 55 92 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 92 150 2 27 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 92 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 53 92 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 92 150 2 26 46 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 92 150
  (Polychromatic418967fa.accept_7_2_1_3_1_102 51 92 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 92 150 2 25 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 92 150 (accept_3_4 49 92 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 92
  150 2 24 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  92 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 92 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 92 150 2 23 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 92 150 (Polychromatic418967fa.accept_12_9_8_6_1_466 45 92 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 92 150 2 22 46 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 92 150 (accept_3_4 43 92 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 92 150 2 21 46 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 92 150
  (Polychromatic418967fa.accept_9_5_2_6_1_265 41 92 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 92 150 2 20 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 92 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 92 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 92 150 2 19 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 92 150 (accept_3_4 37 92 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 92 150 2 18 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 92 150 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 92 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 92 150 2 17 46 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 92 150
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 92 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 92 150 2 16 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 92 150 (accept_3_4 31 92 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 92
  150 2 15 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  92 150 (Polychromatic418967fa.accept_13_3_1_7_1_1706 29 92 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 92 150 2 14 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 92 150 (Polychromatic418967fa.accept_12_3_8_6_1_895 27 92 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 92 150 2 13 46 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 92 150 (accept_3_4 25 92 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 92 150 2 12 46 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 92 150
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 92 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 92 150 2 11 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 92 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 92 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 92 150 2 10 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 92 150 (accept_3_4 19 92 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92 150 2 9 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 92 150 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 92 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 92 150 2 8 46 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 92 150
  (Polychromatic418967fa.accept_12_3_8_6_1_895 15 92 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 92 150 2 7 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 92 150 (accept_3_4 13 92 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92
  150 2 6 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  92 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 92 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 92 150 2 5 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 92 150 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 92 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 92 150 2 4 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 92 150 (accept_3_4 7 92 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 150 2 3 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 92 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 92 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 92 150 2 2 46 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 92 150
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 92 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 92 150 2 1 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 92 150 (accept_3_4 1 92 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  150))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 91 150 (Eq.refl Bool.true)
  (allA_succ_of_accept 59 91 150 (accept_3_5 59 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  91 150 (Polychromatic418967fa.accept_9_4_1_6_1_284 58 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 91 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 91 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 91 150 (accept_3_5 56 91 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 91 150 (Polychromatic418967fa.accept_20_15_11_10_1_5071 55 91 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 91 150
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 54 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 91 150 (accept_3_5 53 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  91 150 (Polychromatic418967fa.accept_9_7_1_6_1_261 52 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 91 150 (Polychromatic418967fa.accept_16_3_11_6_1_4467 51 91 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 150 (accept_3_5 50 91 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 91 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 91 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 91 150
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 91 150 (accept_3_5 47 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  91 150 (Polychromatic418967fa.accept_14_4_7_10_1_3888 46 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 91 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 91 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 150 (accept_3_5 44 91 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 150 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 91 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 91 150
  (Polychromatic418967fa.accept_17_8_6_14_1_6718 42 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 91 150 (accept_3_5 41 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  91 150 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 91 150 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 91 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 150 (accept_3_5 38 91 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 91 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 150
  (Polychromatic418967fa.accept_16_4_11_6_1_5591 36 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 91 150 (accept_3_5 35 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  91 150 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 91 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 91 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 150 (accept_3_5 32 91 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 150 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 91 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 150
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 150 (accept_3_5 29 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  91 150 (Polychromatic418967fa.accept_22_6_3_18_1_8074 28 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 91 150 (Polychromatic418967fa.accept_18_9_1_6_1_5301 27 91 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 150 (accept_3_5 26 91 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 91 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 150
  (Polychromatic418967fa.accept_17_7_6_14_1_6737 24 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 150 (accept_3_5 23 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 150 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 91 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 150 (accept_3_5 20 91 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 150 (Polychromatic418967fa.accept_16_3_11_6_1_4467 19 91 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 150
  (Polychromatic418967fa.accept_14_4_7_10_1_3888 18 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 91 150 (accept_3_5 17 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  91 150 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 150 (Polychromatic418967fa.accept_11_4_3_7_1_828 15 91 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 150 (accept_3_5 14 91 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 91 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 150
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 150 (accept_3_5 11 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 150 (Polychromatic418967fa.accept_11_10_3_7_1_2564 10 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 91 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 150 (accept_3_5 8 91 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 150 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 91 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 150
  (Polychromatic418967fa.accept_21_6_7_3_1_8073 6 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 150 (accept_3_5 5 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  150 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 91 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 91 150 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 91 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 150 (accept_3_5 2 91 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 91 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 91 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91 150))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 61 90 150 (Eq.refl Bool.true) (allA_succ_of_gcd 60 90 150 30 2 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 150 (Polychromatic418967fa.accept_14_3_6_10_1_752
  59 90 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 90 150 2 29 45 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 90 150 3 19 30 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 90 150 2 28 45 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 90 150 5 11 18 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 90 150 6 9 15 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 90 150
  (Polychromatic418967fa.accept_7_4_6_3_1_271 53 90 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 90 150 2 26 45 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 51 90 150 3 17 30 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 90 150 10 5 9 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 90 150 (Polychromatic418967fa.accept_13_10_12_7_1_1079 49 90 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 150 6 8 15 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 150 (Polychromatic418967fa.accept_13_8_12_7_1_2442 47 90 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90 150 2 23 45 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 90 150 15 3 6 10 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 90 150 2 22 45 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 90 150
  (Polychromatic418967fa.accept_13_4_12_7_1_2439 43 90 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 90 150 6 7 15 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 90 150 (Polychromatic418967fa.accept_19_3_14_17_1_6603 41 90 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 150 10 4 9 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 90 150 3 13 30 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 90 150 2 19 45 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 90 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 90 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90 150 6 6 15 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 90 150 5 7 18 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 90 150 2 17 45 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 90 150 3 11 30 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 90 150 2 16 45 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 90 150
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 31 90 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 90 150 30 1 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 90 150 (Polychromatic418967fa.accept_21_8_6_3_1_4881 29 90 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 150 2 14 45 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 90 150 3 9 30 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 90 150 2 13 45 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 90 150 5 5 18 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 90 150 6 4 15 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 23
  90 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 150 2 11 45 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 90 150 3 7 30 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 90 150 10 2 9 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 150
  (Polychromatic418967fa.accept_13_6_12_7_1_5131 19 90 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 150 6 3 15 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 150 (Polychromatic418967fa.accept_13_4_12_7_1_2439 17 90 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 150 2 8 45 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 90 150 15 1 6 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 90 150 2 7 45 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 150 (Polychromatic418967fa.accept_21_13_6_3_1_3381 13 90 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 150 6 2 15 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 150
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 90 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 90 150 10 1 9 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 90 150 3 3 30 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 90 150 2 4 45 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 90 150 (Polychromatic418967fa.accept_21_7_6_3_1_8072 7 90 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 150 6 1 15 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 90 150 5 1 18 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 90 150 2 2 45 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 90 150 3 1 30 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 90 150 2 1 45 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 150 (Polychromatic418967fa.accept_19_1_14_17_1_6605 1 90 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  150))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 89 150 (Eq.refl Bool.true)
  (allA_succ_of_accept 61 89 150 (accept_3_4 61 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  89 150 (Polychromatic418967fa.accept_17_9_4_14_1_4302 60 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 89 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 89 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 89 150 (accept_3_4 58 89 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 89 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 89 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 89 150
  (Polychromatic418967fa.accept_9_2_8_6_1_79 56 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 89 150 (accept_3_4 55 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  89 150 (Polychromatic418967fa.accept_14_12_5_10_1_2130 54 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 89 150 (Polychromatic418967fa.accept_13_1_11_7_1_1704 53 89 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 89 150 (accept_3_4 52 89 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 89 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 89 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 89 150
  (Polychromatic418967fa.accept_7_1_5_3_1_268 50 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 89 150 (accept_3_4 49 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  89 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 89 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 89 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 89 150 (accept_3_4 46 89 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 89 150 (Polychromatic418967fa.accept_16_13_9_6_1_2306 45 89 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 89 150
  (Polychromatic418967fa.accept_7_2_5_3_1_98 44 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 89 150 (accept_3_4 43 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  89 150 (Polychromatic418967fa.accept_13_3_11_7_1_2488 42 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 89 150 (Polychromatic418967fa.accept_9_5_8_6_1_281 41 89 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 89 150 (accept_3_4 40 89 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 89 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 89 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 89 150
  (Polychromatic418967fa.accept_9_2_8_6_1_79 38 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 89 150 (accept_3_4 37 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  89 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 89 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 89 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 89 150 (accept_3_4 34 89 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 89 150 (Polychromatic418967fa.accept_18_15_17_6_1_4043 33 89 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 89 150
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 89 150 (accept_3_4 31 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  89 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 89 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 89 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 89 150 (accept_3_4 28 89 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 89 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 89 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 89 150
  (Polychromatic418967fa.accept_14_12_5_10_1_2130 26 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 89 150 (accept_3_4 25 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  89 150 (Polychromatic418967fa.accept_17_7_4_14_1_2106 24 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 89 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 89 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 89 150 (accept_3_4 22 89 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 89 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 89 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 89 150
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 89 150 (accept_3_4 19 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  89 150 (Polychromatic418967fa.accept_13_5_11_7_1_559 18 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 89 150 (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 89 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 89 150 (accept_3_4 16 89 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 89 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 89 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 150
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 89 150 (accept_3_4 13 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  89 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 89 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 89 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 89 150 (accept_3_4 10 89 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 89 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 89 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 150
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 89 150 (accept_3_4 7 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89
  150 (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 89 150 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 89 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 150 (accept_3_4 4 89 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 89 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 89 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 150
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 89 150 (accept_3_4 1 89 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89
  150)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 88 150 (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 88 150 2 31 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 88 150 (Polychromatic418967fa.accept_24_13_16_6_1_8032 61 88 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 88 150 2 30 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 88 150 (accept_3_5 59 88 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 88 150 2 29 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 88 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 88 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 88 150 2 28 44 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 88 150
  (Polychromatic418967fa.accept_7_6_4_3_1_266 55 88 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 88 150 2 27 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 88 150 (accept_3_5 53 88 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 88
  150 2 26 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  88 150 (Polychromatic418967fa.accept_12_3_4_6_1_434 51 88 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 88 150 2 25 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 88 150 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 88 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 88 150 2 24 44 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 88 150 (accept_3_5 47 88 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 88 150 2 23 44 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 88 150
  (Polychromatic418967fa.accept_12_9_4_6_1_460 45 88 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 88 150 2 22 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 88 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 88 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 88 150 2 21 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 88 150 (accept_3_5 41 88 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 88 150 2 20 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 88 150 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 88 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 88 150 2 19 44 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 88 150
  (Polychromatic418967fa.accept_9_1_7_6_1_75 37 88 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 88 150 2 18 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 88 150 (accept_3_5 35 88 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 88
  150 2 17 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  88 150 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 88 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 88 150 2 16 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 88 150 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 88 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 88 150 2 15 44 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 88 150 (accept_3_5 29 88 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 88 150 2 14 44 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 88 150
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 88 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 88 150 2 13 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 88 150 (Polychromatic418967fa.accept_13_12_10_7_1_2433 25 88 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 88 150 2 12 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 88 150 (accept_3_5 23 88 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88 150 2 11 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 88 150 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 88 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 88 150 2 10 44 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 88 150
  (Polychromatic418967fa.accept_9_1_7_6_1_75 19 88 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 88 150 2 9 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 88 150 (accept_3_5 17 88 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88
  150 2 8 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  88 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 88 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 88 150 2 7 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 88 150 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 88 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 88 150 2 6 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 88 150 (accept_3_5 11 88 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 88 150 2 5 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 88 150 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 88 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 88 150 2 4 44 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 88 150
  (Polychromatic418967fa.accept_14_7_4_10_1_1351 7 88 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 88 150 2 3 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 88 150 (accept_3_5 5 88 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 150
  2 2 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 88
  150 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 88 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 88 150 2 1 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 88 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 88 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 88 150)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 64 87 150 (Eq.refl Bool.true) (allA_succ_of_gcd 63 87 150 3 21 29 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 87 150
  (Polychromatic418967fa.accept_12_2_3_6_1_112 62 87 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 87 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 87 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 87 150 3 20 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 87 150 (Polychromatic418967fa.accept_18_5_15_6_1_3999
  59 87 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 150
  (Polychromatic418967fa.accept_11_3_10_7_1_129 58 87 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 87 150 3 19 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 87 150 (Polychromatic418967fa.accept_12_8_3_6_1_909 56 87 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 150 (Polychromatic418967fa.accept_13_3_9_7_1_1730 55 87 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 87 150 3 18 29 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 87 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 87 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 87 150 (Polychromatic418967fa.accept_12_4_3_6_1_879 52 87 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 87 150 3 17 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 87 150 (Polychromatic418967fa.accept_12_2_3_6_1_112 50
  87 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 87 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 87 150 3 16 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 87 150 (Polychromatic418967fa.accept_11_3_10_7_1_129 47 87 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 150 (Polychromatic418967fa.accept_12_10_3_6_1_882 46 87 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 87 150 3 15 29 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 87 150
  (Polychromatic418967fa.accept_12_8_3_6_1_909 44 87 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 150 (Polychromatic418967fa.accept_13_4_9_7_1_2402 43 87 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 87 150 3 14 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 87 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 87
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 150
  (Polychromatic418967fa.accept_12_4_3_6_1_879 40 87 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 87 150 3 13 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 87 150 (Polychromatic418967fa.accept_12_2_3_6_1_112 38 87 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 87 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 87 150 3 12 29 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 87 150
  (Polychromatic418967fa.accept_14_7_3_10_1_1364 35 87 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 87 150 (Polychromatic418967fa.accept_12_10_3_6_1_882 34 87 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 87 150 3 11 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 87 150 (Polychromatic418967fa.accept_12_8_3_6_1_909 32
  87 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 150
  (Polychromatic418967fa.accept_16_15_7_6_1_1453 31 87 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 87 150 3 10 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 87 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 87 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 150 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 87 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 87 150 3 9 29 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 87 150
  (Polychromatic418967fa.accept_12_2_3_6_1_112 26 87 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 87 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 87 150 3 8 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 87 150 (Polychromatic418967fa.accept_18_5_15_6_1_3999 23 87 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 150
  (Polychromatic418967fa.accept_12_10_3_6_1_882 22 87 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 87 150 3 7 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 87 150 (Polychromatic418967fa.accept_12_8_3_6_1_909 20 87 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 150 (Polychromatic418967fa.accept_13_6_9_7_1_2430 19 87 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 150 3 6 29 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 87 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 150 (Polychromatic418967fa.accept_12_4_3_6_1_879 16 87 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 87 150 3 5 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 87 150 (Polychromatic418967fa.accept_11_3_10_7_1_129 14 87 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 87 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 87 150 3 4 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 87 150 (Polychromatic418967fa.accept_13_11_9_7_1_2484 11 87 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 150 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 87 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 150 3 3 29 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 150
  (Polychromatic418967fa.accept_12_8_3_6_1_909 8 87 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 150 (Polychromatic418967fa.accept_14_7_3_10_1_1364 7 87 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 87 150 3 2 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 87 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 87 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 150
  (Polychromatic418967fa.accept_12_4_3_6_1_879 4 87 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 87 150 3 1 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 87 150 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 87 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 87 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  150)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 86 150 (Eq.refl Bool.true)
  (allA_succ_of_gcd 64 86 150 2 32 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 86 150 (Polychromatic418967fa.accept_12_3_2_6_1_138 63 86 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 86 150 2 31 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 86 150 (accept_3_4 61 86 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 86 150 2 30 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 86 150 (Polychromatic418967fa.accept_19_2_10_17_1_3876 59 86
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 86 150 2 29 43 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 86 150
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 86 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 86 150 2 28 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 86 150 (accept_3_4 55 86 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 86
  150 2 27 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  86 150 (Polychromatic418967fa.accept_9_8_5_6_1_538 53 86 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 86 150 2 26 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 86 150 (Polychromatic418967fa.accept_12_3_2_6_1_138 51 86 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 86 150 2 25 43 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 86 150 (accept_3_4 49 86 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 86 150 2 24 43 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 86 150
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 86 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 86 150 2 23 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 86 150 (Polychromatic418967fa.accept_12_9_2_6_1_455 45 86 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 86 150 2 22 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 86 150 (accept_3_4 43 86 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 86 150 2 21 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 86 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 86 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 86 150 2 20 43 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 86 150
  (Polychromatic418967fa.accept_9_3_5_6_1_253 39 86 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 86 150 2 19 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 86 150 (accept_3_4 37 86 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 86
  150 2 18 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  86 150 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 86 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 86 150 2 17 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 86 150 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 86 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 86 150 2 16 43 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 86 150 (accept_3_4 31 86 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 86 150 2 15 43 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 86 150
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 86 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 86 150 2 14 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 86 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 86 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 86 150 2 13 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 86 150 (accept_3_4 25 86 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 86 150 2 12 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 86 150 (Polychromatic418967fa.accept_13_10_8_7_1_1074 23 86 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 86 150 2 11 43 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 86 150
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 86 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 86 150 2 10 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 86 150 (accept_3_4 19 86 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 86
  150 2 9 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  86 150 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 86 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 86 150 2 8 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 86 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 86 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 86 150 2 7 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 86 150 (accept_3_4 13 86 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86 150 2 6 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 86 150 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 86 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 86 150 2 5 43 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 86 150
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 86 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 86 150 2 4 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 86 150 (accept_3_4 7 86 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 86 150
  2 3 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 86
  150 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 86 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 86 150 2 2 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 86 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 86 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 86 150 2 1 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 86 150 (accept_3_4 1 86 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 86 150))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 85 150
  (Eq.refl Bool.true) (allA_succ_of_gcd 65 85 150 5 13 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 64 85 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 64 85 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 85 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 85 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 85 150 (accept_3_5 62 85 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  85 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 85 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 85 150 5 12 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 85 150 (accept_3_5 59 85 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 85 150 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 85 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 85 150 (Polychromatic418967fa.accept_9_3_4_6_1_252 57 85 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 150 (accept_3_5 56 85 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 85 150 5 11 17 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 85 150
  (Polychromatic418967fa.accept_7_5_1_3_1_103 54 85 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 85 150 (accept_3_5 53 85 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  85 150 (Polychromatic418967fa.accept_9_7_4_6_1_273 52 85 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 85 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 85 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 85 150 5 10 17 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 85 150
  (Polychromatic418967fa.accept_16_1_5_6_1_4435 49 85 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 85 150 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 85 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 150 (accept_3_5 47 85 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 85 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 85 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 85 150 5 9 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 85 150 (accept_3_5 44 85 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 85 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 150
  (Polychromatic418967fa.accept_20_2_5_10_1_3535 42 85 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 150 (accept_3_5 41 85 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 85
  150 5 8 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  85 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 85 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 85 150 (accept_3_5 38 85 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 85 150 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 85 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 150 (Polychromatic418967fa.accept_16_4_5_6_1_8071 36 85 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 85 150 5 7 17 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 85 150
  (Polychromatic418967fa.accept_9_7_4_6_1_273 34 85 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 85 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 85 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 150 (accept_3_5 32 85 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 85 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 85 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 85 150 5 6 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 85 150 (accept_3_5 29 85 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 85 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 85 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 85 150 (accept_3_5 26 85 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 85
  150 5 5 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  85 150 (Polychromatic418967fa.accept_20_4_5_10_1_2308 24 85 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 85 150 (accept_3_5 23 85 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 85 150 (Polychromatic418967fa.accept_20_2_5_10_1_3535 22 85 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 150 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 85 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 85 150 5 4 17 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 85 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 85 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 85 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 85 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 150 (accept_3_5 17 85 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 85 150 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 85 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 85 150 5 3 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 85 150 (accept_3_5 14 85 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 150 (Polychromatic418967fa.accept_19_13_9_17_1_8070 13 85 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 150
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 85 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 150 (accept_3_5 11 85 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 85
  150 5 2 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  85 150 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 85 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 85 150 (accept_3_5 8 85 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 85 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 85 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 150 (Polychromatic418967fa.accept_19_6_9_17_1_5214 6 85 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 85 150 5 1 17 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 85 150
  (Polychromatic418967fa.accept_7_4_1_3_1_277 4 85 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 85 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 150 (accept_3_5 2 85 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 85 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  150)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 84 150 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 84 150 6 11 14 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 84 150 (Polychromatic418967fa.accept_9_2_3_6_1_88 65 84 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 84 150 2 32 42 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 84 150 3 21 28 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 84 150 2 31 42 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 84 150 (Polychromatic418967fa.accept_9_7_3_6_1_270 61
  84 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 150 6 10 14 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 150
  (Polychromatic418967fa.accept_9_5_3_6_1_269 59 84 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 84 150 2 29 42 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 84 150 3 19 28 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 56 84 150 2 28 42 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 84 150 (Polychromatic418967fa.accept_9_1_3_6_1_70 55 84 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 150 6 9 14 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 150 (Polychromatic418967fa.accept_9_8_3_6_1_533 53 84 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 84 150 2 26 42 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 84 150 3 17 28 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 84 150 2 25 42 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 84 150
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 84 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 84 150 6 8 14 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 84 150 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 84 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 84 150 2 23 42 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 84 150 3 15 28 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 84 150 2 22 42 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 150 (Polychromatic418967fa.accept_9_7_3_6_1_270 43
  84 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 150 6 7 14 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 150
  (Polychromatic418967fa.accept_9_5_3_6_1_269 41 84 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 84 150 2 20 42 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 84 150 3 13 28 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 84 150 2 19 42 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 84 150 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 84 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 150 6 6 14 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 84 150 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 84 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84 150 2 17 42 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 84 150 3 11 28 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 84 150 2 16 42 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 150
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 84 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 84 150 6 5 14 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 84 150 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 84 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 150 2 14 42 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 84 150 3 9 28 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 84 150 2 13 42 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 150 (Polychromatic418967fa.accept_9_7_3_6_1_270 25
  84 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 150 6 4 14 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 150
  (Polychromatic418967fa.accept_9_5_3_6_1_269 23 84 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 84 150 2 11 42 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 84 150 3 7 28 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 84 150 2 10 42 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 84 150 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 84 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 150 6 3 14 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 150 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 84 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84 150 2 8 42 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 84 150 3 5 28 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 84 150 2 7 42 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 150
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 84 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 84 150 6 2 14 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 84 150 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 84 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 150 2 5 42 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 84 150 3 3 28 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 84 150 2 4 42 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 84 150 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 84 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 150 6 1 14 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 150
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 84 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 84 150 2 2 42 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 84 150 3 1 28 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 84 150 2 1 42 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 84 150 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 84 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 84 150)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 68 83 150 (Eq.refl Bool.true) (allA_succ_of_accept 67 83 150 (accept_3_4 67 83 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 66 83 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 150 (accept_3_4 64 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 150 (Polychromatic418967fa.accept_13_11_5_7_1_2420 63 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 150 (Polychromatic418967fa.accept_9_8_2_6_1_875 62 83 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 150 (accept_3_4 61 83 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 150 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 83 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 150
  (Polychromatic418967fa.accept_9_5_2_6_1_265 59 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 150 (accept_3_4 58 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 150 (Polychromatic418967fa.accept_11_1_6_7_1_116 56 83 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 150 (accept_3_4 55 83 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 150 (Polychromatic418967fa.accept_13_2_5_7_1_1695 54 83 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 150 (accept_3_4 52 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 150 (Polychromatic418967fa.accept_9_5_2_6_1_265 50 83 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 150 (accept_3_4 49 83 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 83 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 150
  (Polychromatic418967fa.accept_19_9_7_17_1_3875 47 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 150 (accept_3_4 46 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 83 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 150 (accept_3_4 43 83 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 150 (Polychromatic418967fa.accept_20_2_3_10_1_5075 42 83 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 150 (accept_3_4 40 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 150 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 150 (Polychromatic418967fa.accept_13_12_5_7_1_1696 38 83 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 150 (accept_3_4 37 83 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 150 (Polychromatic418967fa.accept_16_4_3_6_1_6805 36 83 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 150
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 150 (accept_3_4 34 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 150 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 83 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 150 (accept_3_4 31 83 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 83 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 150 (accept_3_4 28 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 150 (Polychromatic418967fa.accept_16_11_3_6_1_4462 27 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 150 (Polychromatic418967fa.accept_9_8_2_6_1_875 26 83 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 150 (accept_3_4 25 83 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 150 (Polychromatic418967fa.accept_13_11_5_7_1_2420 24 83 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 150
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 150 (accept_3_4 22 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 150 (Polychromatic418967fa.accept_16_4_3_6_1_6805 20 83 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 150 (accept_3_4 19 83 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 150 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 83 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 150 (accept_3_4 16 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 150 (Polychromatic418967fa.accept_13_2_5_7_1_1695 15 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 150 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 83 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 150 (accept_3_4 13 83 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 83 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 150
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 150 (accept_3_4 10 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 83 150 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 83 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 150 (accept_3_4 7 83 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 83 150 (Polychromatic418967fa.accept_17_6_15_14_1_8027 6 83 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 83
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 150 (accept_3_4 4 83 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 3
  83 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 150
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 83 150 (accept_3_4 1 83 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83
  150)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 82 150 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 82 150 2 34 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 82 150 (Polychromatic418967fa.accept_9_4_1_6_1_284 67 82 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 82 150 2 33 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 82 150 (accept_3_5 65 82 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 82 150 2 32 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 82 150 (Polychromatic418967fa.accept_12_3_10_6_1_442 63 82 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 82 150 2 31 41 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 82 150
  (Polychromatic418967fa.accept_9_7_1_6_1_261 61 82 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 82 150 2 30 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 82 150 (accept_3_5 59 82 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 82
  150 2 29 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  82 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 82 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 82 150 2 28 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 82 150 (Polychromatic418967fa.accept_13_3_4_7_1_1711 55 82 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 82 150 2 27 41 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 82 150 (accept_3_5 53 82 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 82 150 2 26 41 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 82 150
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 82 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 82 150 2 25 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 82 150 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 82 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 82 150 2 24 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 82 150 (accept_3_5 47 82 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 82 150 2 23 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 82 150 (Polychromatic418967fa.accept_12_9_10_6_1_872 45 82 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 82 150 2 22 41 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 82 150
  (Polychromatic418967fa.accept_7_1_5_3_1_268 43 82 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 82 150 2 21 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 82 150 (accept_3_5 41 82 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 82
  150 2 20 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  82 150 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 82 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 82 150 2 19 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 82 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 82 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 82 150 2 18 41 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 82 150 (accept_3_5 35 82 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 82 150 2 17 41 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 82 150
  (Polychromatic418967fa.accept_12_9_10_6_1_872 33 82 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 82 150 2 16 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 82 150 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 82 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 82 150 2 15 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 82 150 (accept_3_5 29 82 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 82 150 2 14 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 82 150 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 82 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 82 150 2 13 41 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 82 150
  (Polychromatic418967fa.accept_9_7_1_6_1_261 25 82 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 82 150 2 12 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 82 150 (accept_3_5 23 82 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 82
  150 2 11 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  82 150 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 82 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 82 150 2 10 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 82 150 (Polychromatic418967fa.accept_13_6_4_7_1_2464 19 82 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 82 150 2 9 41 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 82 150 (accept_3_5 17 82 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 82 150 2 8 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 82 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 82 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 82 150 2 7 41 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 82 150
  (Polychromatic418967fa.accept_9_4_1_6_1_284 13 82 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 82 150 2 6 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 82 150 (accept_3_5 11 82 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82
  150 2 5 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  82 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 82 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 82 150 2 4 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 82 150 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 82 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 150 2 3 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 150 (accept_3_5 5 82 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 82 150 2 2 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 82 150 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 82 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 150 2 1 41 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 150
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 82 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 82 150))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 81 150 (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 81 150 3 23 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 81 150 (Polychromatic418967fa.accept_12_8_9_6_1_127 68 81 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 67
  81 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 81 150 3 22 27 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 81 150
  (Polychromatic418967fa.accept_20_5_1_10_1_6523 65 81 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 81 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 81 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 81 150 3 21 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 81 150 (Polychromatic418967fa.accept_7_6_4_3_1_266 62
  81 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 150
  (Polychromatic418967fa.accept_13_9_3_7_1_1065 61 81 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 81 150 3 20 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 81 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 81 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 150 (Polychromatic418967fa.accept_11_3_4_7_1_114 58 81 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 81 150 3 19 27 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 81 150
  (Polychromatic418967fa.accept_12_8_9_6_1_127 56 81 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 81 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 81 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 81 150 3 18 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 81 150 (Polychromatic418967fa.accept_13_1_3_7_1_1710
  53 81 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 150
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 52 81 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 81 150 3 17 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 81 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 50 81 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 150 (Polychromatic418967fa.accept_13_10_3_7_1_2517 49 81
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 81 150 3 16 27 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 81 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 81 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 81 150 (Polychromatic418967fa.accept_12_10_9_6_1_1445 46 81 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 81 150 3 15 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 81 150 (Polychromatic418967fa.accept_12_8_9_6_1_127 44
  81 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 81 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 81 150 3 14 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 81 150 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 81 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 150 (Polychromatic418967fa.accept_12_4_9_6_1_440 40 81 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 81 150 3 13 27 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 81 150
  (Polychromatic418967fa.accept_12_2_9_6_1_439 38 81 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 81 150 (Polychromatic418967fa.accept_13_11_3_7_1_2513 37 81 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 81 150 3 12 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 81 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 35
  81 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 150
  (Polychromatic418967fa.accept_7_6_4_3_1_266 34 81 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 81 150 3 11 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 81 150 (Polychromatic418967fa.accept_12_8_9_6_1_127 32 81 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 81 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 81 150 3 10 27 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 81 150
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 81 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 150 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 81 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 81 150 3 9 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 81 150 (Polychromatic418967fa.accept_12_2_9_6_1_439 26 81 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 150
  (Polychromatic418967fa.accept_11_3_4_7_1_114 25 81 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 81 150 3 8 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 81 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 81 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 81 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 81 150 3 7 27 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 81 150
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 81 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 81 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 81 150 3 6 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 81 150 (Polychromatic418967fa.accept_13_4_3_7_1_2515 17 81 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 150
  (Polychromatic418967fa.accept_12_4_9_6_1_440 16 81 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 81 150 3 5 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 81 150 (Polychromatic418967fa.accept_11_3_4_7_1_114 14 81 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 150 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 81 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 150 3 4 27 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 81 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 150 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 81 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 81 150 3 3 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 81 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 81 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 81 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 81 150 3 2 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 81 150 (Polychromatic418967fa.accept_16_5_1_6_1_3367 5 81 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 150 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 81 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 150 3 1 27 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 150
  (Polychromatic418967fa.accept_12_2_9_6_1_439 2 81 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 81 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 81 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 81 150))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 71 80 150 (Eq.refl Bool.true) (allA_succ_of_gcd 70 80 150 10 7 8 15 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 80 150
  (Polychromatic418967fa.accept_12_9_8_6_1_466 69 80 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 80 150 2 34 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 80 150 (accept_3_4 67 80 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 80
  150 2 33 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 80
  150 5 13 16 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 80
  150 2 32 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63
  80 150 (Polychromatic418967fa.accept_12_3_8_6_1_895 63 80 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 80 150 2 31 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 80 150 (accept_3_4 61 80 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 80 150 10 6 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 80 150 (Polychromatic418967fa.accept_9_5_8_6_1_281 59 80 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 80 150 2 29 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 80 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 57
  80 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 80 150 2 28 40 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 80 150 5 11 16 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 80 150 2 27 40 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 80 150
  (Polychromatic418967fa.accept_24_5_8_6_1_8069 53 80 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 80 150 2 26 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 80 150 (Polychromatic418967fa.accept_12_3_8_6_1_895 51 80 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 150 10 5 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 150 (accept_3_4 49 80 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 80 150 2 24 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 80 150 (Polychromatic418967fa.accept_9_2_8_6_1_79 47 80 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 80 150 2 23 40 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 80 150 5 9 16 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 80 150 2 22 40 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 80 150 (accept_3_4 43 80 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 80 150 2 21 40 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 80 150
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 80 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 80 150 10 4 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 80 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 80 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 80 150 2 19 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 80 150 (accept_3_4 37 80 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 80 150 2 18 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 80 150 5 7 16 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 80 150 2 17 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 80 150 (Polychromatic418967fa.accept_12_9_8_6_1_466 33 80 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 80 150 2 16 40 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 80 150 (accept_3_4 31
  80 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80 150 10 3 8 15 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 80 150
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 80 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 80 150 2 14 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 80 150 (Polychromatic418967fa.accept_12_3_8_6_1_895 27 80 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 80 150 2 13 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 80 150 5 5 16 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 80 150 2 12 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 80 150 (Polychromatic418967fa.accept_9_5_8_6_1_281 23
  80 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 80 150 2 11 40 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 80 150
  (Polychromatic418967fa.accept_9_3_8_6_1_80 21 80 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 80 150 10 2 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 80 150 (accept_3_4 19 80 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80
  150 2 9 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  80 150 (Polychromatic418967fa.accept_24_17_8_6_1_6246 17 80 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 80 150 2 8 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 80 150 5 3 16 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 80 150 2 7 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 80 150 (accept_3_4 13 80 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 80 150 2 6 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 80 150 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 80 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 150 10 1 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 150 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 80 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 80 150 2 4 40 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 80 150 (accept_3_4 7 80 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 150 2 3 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 80 150 5 1 16 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 80 150 2 2 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 80 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 80
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 150 2 1 40 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 150 (accept_3_4 1 80
  150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  150))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 79 150 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 79 150 (accept_3_5 71 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  79 150 (Polychromatic418967fa.accept_21_7_16_3_1_1058 70 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 79 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 79 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 150 (accept_3_5 68 79 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 150 (Polychromatic418967fa.accept_9_4_7_6_1_255 67 79 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 150
  (Polychromatic418967fa.accept_9_3_7_6_1_76 66 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 150 (accept_3_5 65 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 150 (Polychromatic418967fa.accept_13_11_1_7_1_1691 63 79 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 150 (accept_3_5 62 79 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 79 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 150
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 60 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 79 150 (accept_3_5 59 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  79 150 (Polychromatic418967fa.accept_9_4_7_6_1_255 58 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 79 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 150 (accept_3_5 56 79 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 79 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 150
  (Polychromatic418967fa.accept_7_5_2_3_1_106 54 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 150 (accept_3_5 53 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 150 (Polychromatic418967fa.accept_19_14_3_17_1_6558 52 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 150 (Polychromatic418967fa.accept_20_11_19_10_1_3568 51 79 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 150 (accept_3_5 50 79 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 79 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 150
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 150 (accept_3_5 47 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 150 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 79 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 150 (accept_3_5 44 79 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 79 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 150
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 42 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 150 (accept_3_5 41 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 150 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 150 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 79 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 150 (accept_3_5 38 79 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 79 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 150
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 150 (accept_3_5 35 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 79 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 150 (accept_3_5 32 79 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 150 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 79 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 150
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 150 (accept_3_5 29 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 150 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 79 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 150 (accept_3_5 26 79 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 79 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 150
  (Polychromatic418967fa.accept_13_11_1_7_1_1691 24 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 150 (accept_3_5 23 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 79 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 150 (accept_3_5 20 79 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 150 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 79 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 150
  (Polychromatic418967fa.accept_21_18_16_3_1_8068 18 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 150 (accept_3_5 17 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 150 (Polychromatic418967fa.accept_13_3_1_7_1_1706 16 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 79 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 150 (accept_3_5 14 79 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 79 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 150
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 150 (accept_3_5 11 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 150 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 79 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 150 (accept_3_5 8 79 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 150 (Polychromatic418967fa.accept_16_7_15_6_1_1428 7 79 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 150
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 150 (accept_3_5 5 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  150 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 79 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 150 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 79 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 150 (accept_3_5 2 79 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 79 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  150)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 78 150 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 78 150 6 12 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 78 150 (Polychromatic418967fa.accept_19_14_2_17_1_678 71 78 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 78 150 2 35 39 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 78 150 3 23 26 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 78 150 2 34 39 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 78 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 67
  78 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 150 6 11 13 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 150
  (Polychromatic418967fa.accept_7_2_1_3_1_102 65 78 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 78 150 2 32 39 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 78 150 3 21 26 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 78 150 2 31 39 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 78 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 78 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 78 150 6 10 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 78 150 (Polychromatic418967fa.accept_21_17_15_3_1_4937
  59 78 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78 150 2 29 39 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 78 150 3 19 26 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 78 150 2 28 39 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 78 150
  (Polychromatic418967fa.accept_20_15_18_10_1_8067 55 78 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 78 150 6 9 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 78 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 53 78 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 150 2 26 39 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 78 150 3 17 26 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 78 150 2 25 39 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 78 150
  (Polychromatic418967fa.accept_21_7_15_3_1_8029 49 78 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 78 150 6 8 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 78 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 78 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 150 2 23 39 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 78 150 3 15 26 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 78 150 2 22 39 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 78 150 (Polychromatic418967fa.accept_19_5_2_17_1_8066
  43 78 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78 150 6 7 13 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 78 150
  (Polychromatic418967fa.accept_17_7_10_14_1_8022 41 78 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 78 150 2 20 39 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 78 150 3 13 26 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 78 150 2 19 39 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 78 150 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 78 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 150 6 6 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 150 (Polychromatic418967fa.accept_17_1_10_14_1_1173 35 78
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 150 2 17 39 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 78 150 3 11 26 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 78 150 2 16 39 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 150
  (Polychromatic418967fa.accept_19_12_2_17_1_5210 31 78 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 150 6 5 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 78 150 (Polychromatic418967fa.accept_19_10_2_17_1_675 29 78 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 150 2 14 39 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 78 150 3 9 26 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 78 150 2 13 39 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 25
  78 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 150 6 4 13 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 150
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 78 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 78 150 2 11 39 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 78 150 3 7 26 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 78 150 2 10 39 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 78 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 78 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 150 6 3 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 150 (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 78 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 150 2 8 39 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 78 150 3 5 26 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 78 150 2 7 39 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 150
  (Polychromatic418967fa.accept_17_13_10_14_1_4211 13 78 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 78 150 6 2 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 78 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 78 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78 150 2 5 39 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 78 150 3 3 26 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 78 150 2 4 39 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 150 (Polychromatic418967fa.accept_17_7_10_14_1_8022
  7 78 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 150 6 1 13 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 150
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 78 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 78 150 2 2 39 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 78 150 3 1 26 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 78 150 2 1 39 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 78 150 (Polychromatic418967fa.accept_17_1_10_14_1_1173 1 78 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 78
  150))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 77 150 (Eq.refl Bool.true)
  (allA_succ_of_accept 73 77 150 (accept_3_4 73 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  77 150 (Polychromatic418967fa.accept_17_4_9_14_1_5406 72 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 77 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 77 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 77 150 (accept_3_4 70 77 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 77 150 (Polychromatic418967fa.accept_13_4_12_7_1_2439 69 77 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 77 150
  (Polychromatic418967fa.accept_16_4_13_6_1_4417 68 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 77 150 (accept_3_4 67 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  77 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 66 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 77 150 (Polychromatic418967fa.accept_9_2_5_6_1_536 65 77 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 77 150 (accept_3_4 64 77 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 77 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 77 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 77 150
  (Polychromatic418967fa.accept_9_8_5_6_1_538 62 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 77 150 (accept_3_4 61 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  77 150 (Polychromatic418967fa.accept_13_8_12_7_1_2442 60 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 77 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 77 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 77 150 (accept_3_4 58 77 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 77 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 57 77 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 77 150
  (Polychromatic418967fa.accept_9_2_5_6_1_536 56 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 77 150 (accept_3_4 55 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  77 150 (Polychromatic418967fa.accept_19_16_1_17_1_8065 54 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 77 150 (Polychromatic418967fa.accept_9_8_5_6_1_538 53 77 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 77 150 (accept_3_4 52 77 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 77 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 77 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 77 150
  (Polychromatic418967fa.accept_13_11_12_7_1_2443 50 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 77 150 (accept_3_4 49 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  77 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 77 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 77 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 77 150 (accept_3_4 46 77 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 77 150 (Polychromatic418967fa.accept_13_6_12_7_1_5131 45 77 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 77 150
  (Polychromatic418967fa.accept_9_8_5_6_1_538 44 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 77 150 (accept_3_4 43 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  77 150 (Polychromatic418967fa.accept_19_4_1_17_1_8064 42 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 77 150 (Polychromatic418967fa.accept_16_9_13_6_1_2334 41 77 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 77 150 (accept_3_4 40 77 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 77 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 77 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 77 150
  (Polychromatic418967fa.accept_9_2_5_6_1_536 38 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 77 150 (accept_3_4 37 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  77 150 (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 77 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 77 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 77 150 (accept_3_4 34 77 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 77 150 (Polychromatic418967fa.accept_18_15_5_6_1_5293 33 77 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 77 150
  (Polychromatic418967fa.accept_13_6_12_7_1_5131 32 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 77 150 (accept_3_4 31 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  77 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 77 150 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 77 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 77 150 (accept_3_4 28 77 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 77 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 77 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 150
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 77 150 (accept_3_4 25 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  77 150 (Polychromatic418967fa.accept_13_11_12_7_1_2443 24 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 77 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 77 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 77 150 (accept_3_4 22 77 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 77 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 77 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 77 150
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 77 150 (accept_3_4 19 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  77 150 (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 77 150 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 77 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 77 150 (accept_3_4 16 77 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 77 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 77 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 77 150
  (Polychromatic418967fa.accept_19_14_1_17_1_8063 14 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 77 150 (accept_3_4 13 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  77 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 77 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 77 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 77 150 (accept_3_4 10 77 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 77 150 (Polychromatic418967fa.accept_16_9_13_6_1_2334 9 77 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 150
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 77 150 (accept_3_4 7 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 77
  150 (Polychromatic418967fa.accept_13_6_12_7_1_5131 6 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 77 150 (Polychromatic418967fa.accept_13_5_12_7_1_1080 5 77 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 150 (accept_3_4 4 77 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 77 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 77 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 150
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 77 150 (accept_3_4 1 77 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77
  150)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 76 150 (Eq.refl
  Bool.true) (allA_succ_of_gcd 74 76 150 2 37 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 76 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 73 76 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 76 150 2 36 38 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 76 150 (accept_3_5 71 76 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 76 150 2 35 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 76 150 (Polychromatic418967fa.accept_11_3_10_7_1_129
  69 76 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 76 150 2 34 38 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 76 150
  (Polychromatic418967fa.accept_7_4_6_3_1_271 67 76 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 76 150 2 33 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 76 150 (accept_3_5 65 76 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 76
  150 2 32 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63
  76 150 (Polychromatic418967fa.accept_12_3_4_6_1_434 63 76 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 76 150 2 31 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 76 150 (Polychromatic418967fa.accept_9_7_4_6_1_273 61 76 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 76 150 2 30 38 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 76 150 (accept_3_5 59 76 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 76 150 2 29 38 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 76 150
  (Polychromatic418967fa.accept_9_3_4_6_1_252 57 76 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 76 150 2 28 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 76 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 76 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 76 150 2 27 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 76 150 (accept_3_5 53 76 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 76 150 2 26 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 76 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 76 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 76 150 2 25 38 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 76 150
  (Polychromatic418967fa.accept_20_9_16_10_1_3559 49 76 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 76 150 2 24 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 76 150 (accept_3_5 47 76 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 76
  150 2 23 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  76 150 (Polychromatic418967fa.accept_12_9_4_6_1_460 45 76 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 76 150 2 22 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 76 150 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 76 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 76 150 2 21 38 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 76 150 (accept_3_5 41 76 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 76 150 2 20 38 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 76 150
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 76 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 76 150 2 19 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 76 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 76 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 76 150 2 18 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 76 150 (accept_3_5 35 76 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 76 150 2 17 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 76 150 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 76 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 76 150 2 16 38 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 76 150
  (Polychromatic418967fa.accept_13_5_11_7_1_559 31 76 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 76 150 2 15 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 76 150 (accept_3_5 29 76 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 76
  150 2 14 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  76 150 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 76 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 76 150 2 13 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 76 150 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 76 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 76 150 2 12 38 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 76 150 (accept_3_5 23 76 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76 150 2 11 38 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 76 150
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 76 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 76 150 2 10 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 76 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 76 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 76 150 2 9 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 76 150 (accept_3_5 17 76 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 76 150 2 8 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 76 150 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 76 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 76 150 2 7 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 76 150
  (Polychromatic418967fa.accept_26_13_24_20_1_8062 13 76 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 76 150 2 6 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 76 150 (accept_3_5 11 76 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 76 150 2 5 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 76 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 76 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 76 150 2 4 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 76 150 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 76 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 76 150 2 3 38 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 76 150 (accept_3_5 5 76 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 150 2 2 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 76 150 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 76
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 76 150 2 1 38 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 76 150
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 76 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 76 150))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 150
  (allA_succ_of_accept 74 75 150 (Polychromatic418967fa.accept_9_2_3_6_1_88 74 75 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 75 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 75 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 75 150 3 24 25 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 75 150
  (Polychromatic418967fa.accept_7_1_5_3_1_268 71 75 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 75 150 5 14 15 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 69 75 150 3 23 25 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 75 150 (Polychromatic418967fa.accept_9_5_3_6_1_269 68 75 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 150 (Polychromatic418967fa.accept_9_4_3_6_1_532 67 75 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 75 150 3 22 25 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 75 150 5 13 15 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 75 150
  (Polychromatic418967fa.accept_7_1_5_3_1_268 64 75 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 75 150 3 21 25 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 75 150 (Polychromatic418967fa.accept_9_8_3_6_1_533 62 75 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 75 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 150 15 4 5 10 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 150
  (Polychromatic418967fa.accept_9_5_3_6_1_269 59 75 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 75 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 75 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 75 150 3 19 25 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 75 150 (Polychromatic418967fa.accept_9_2_3_6_1_88 56
  75 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 75 150 5 11 15 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 75 150 3 18 25 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 75 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 75 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 75 150 (Polychromatic418967fa.accept_9_7_3_6_1_270 52 75 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 75 150 3 17 25 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 75 150 25 2 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 75 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 75
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 75 150 3 16 25 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 75 150
  (Polychromatic418967fa.accept_9_2_3_6_1_88 47 75 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 75 150 (Polychromatic418967fa.accept_9_1_3_6_1_70 46 75 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 150 15 3 5 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 75 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 150
  (Polychromatic418967fa.accept_7_1_5_3_1_268 43 75 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 75 150 3 14 25 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 75 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 75 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 75 150 5 8 15 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 75 150 3 13 25 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 75 150 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 75 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 37 75 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 75 150 3 12 25 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 75 150 5 7 15 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 75 150 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 75 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 75 150 3 11 25 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 75 150 (Polychromatic418967fa.accept_9_5_3_6_1_269 32
  75 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 150
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 75 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 75 150 15 2 5 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 75 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 75 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 150 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 75 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 75 150 3 9 25 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 75 150
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 75 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 75 150 25 1 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 75 150 3 8 25 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 75 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 75 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 75 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 75 150 3 7 25 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 75 150 5 4 15 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 75 150
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 75 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 75 150 3 6 25 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 75 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 75 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 75 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 150 15 1 5 10 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 150
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 75 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 75 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 75 150 3 4 25 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 75 150 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 75 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 75 150 5 2 15 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 75 150 3 3 25 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 150
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 75 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 150 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 75 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 150 3 2 25 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 75 150 5 1 15 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 75 150 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 75 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 75 150 3 1 25 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 75 150
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 75 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 75 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 75 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 75
  150))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 150 (allA_succ_of_accept
  73 74 150 (accept_3_4 73 74 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 74 150 2 36 37 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 74 150
  (Polychromatic418967fa.accept_7_1_4_3_1_21 71 74 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 74 150 2 35 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 74 150 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 74 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 74 150 2 34 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 74 150 (accept_3_4 67 74 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 74 150 2 33 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 74 150 (Polychromatic418967fa.accept_20_5_14_10_1_1269 65 74
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 74 150 2 32 37 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 74 150
  (Polychromatic418967fa.accept_12_3_2_6_1_138 63 74 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 74 150 2 31 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 74 150 (accept_3_4 61 74 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 74
  150 2 30 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  74 150 (Polychromatic418967fa.accept_9_5_2_6_1_265 59 74 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 74 150 2 29 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 74 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 74 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 74 150 2 28 37 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 74 150 (accept_3_4 55 74 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 74 150 2 27 37 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 74 150
  (Polychromatic418967fa.accept_9_8_2_6_1_875 53 74 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 74 150 2 26 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 74 150 (Polychromatic418967fa.accept_12_3_2_6_1_138 51 74 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 74 150 2 25 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 74 150 (accept_3_4 49 74 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 74 150 2 24 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 74 150 (Polychromatic418967fa.accept_13_8_9_7_1_530 47 74 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 74 150 2 23 37 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 74 150
  (Polychromatic418967fa.accept_12_9_2_6_1_455 45 74 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 74 150 2 22 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 74 150 (accept_3_4 43 74 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 74
  150 2 21 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  74 150 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 74 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 74 150 2 20 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 74 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 74 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 74 150 2 19 37 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 74 150 (accept_3_4 37 74 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 74 150 2 18 37 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 74 150
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 74 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 74 150 2 17 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 74 150 (Polychromatic418967fa.accept_12_9_2_6_1_455 33 74 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 74 150 2 16 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 74 150 (accept_3_4 31 74 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 74 150 2 15 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 74 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 74 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 74 150 2 14 37 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 74 150
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 74 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 74 150 2 13 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 74 150 (accept_3_4 25 74 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 74
  150 2 12 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  74 150 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 74 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 74 150 2 11 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 74 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 74 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 74 150 2 10 37 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 74 150 (accept_3_4 19 74 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 74 150 2 9 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 74 150 (Polychromatic418967fa.accept_9_8_2_6_1_875 17
  74 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 150 2 8 37 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 150
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 74 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 74 150 2 7 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 74 150 (accept_3_4 13 74 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74
  150 2 6 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  74 150 (Polychromatic418967fa.accept_13_11_9_7_1_2484 11 74 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 74 150 2 5 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 74 150 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 74 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 150 2 4 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 150 (accept_3_4 7 74 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 150 2 3 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 74 150 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 74 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 150 2 2 37 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 150
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 74 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 74 150 2 1 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 74 150 (accept_3_4 1 74 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  150)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 150 (allA_succ_of_accept
  72 73 150 (Polychromatic418967fa.accept_20_12_13_10_1_8061 72 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 73 150 (accept_3_5 71 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 73 150 (Polychromatic418967fa.accept_9_7_1_6_1_261 70 73 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 73 150 (Polychromatic418967fa.accept_14_13_3_10_1_2159 69 73
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 150 (accept_3_5 68 73 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 67
  73 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 150
  (Polychromatic418967fa.accept_9_3_1_6_1_86 66 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 150 (accept_3_5 65 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 150 (Polychromatic418967fa.accept_13_12_8_7_1_2526 64 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 73 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 150 (accept_3_5 62 73 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 150 (Polychromatic418967fa.accept_9_7_1_6_1_261 61 73 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 150
  (Polychromatic418967fa.accept_17_9_5_14_1_4277 60 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 150 (accept_3_5 59 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 150 (Polychromatic418967fa.accept_9_4_1_6_1_284 58 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 150 (Polychromatic418967fa.accept_9_3_1_6_1_86 57 73 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 150 (accept_3_5 56 73 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 73 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 150
  (Polychromatic418967fa.accept_13_2_8_7_1_2424 54 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 150 (accept_3_5 53 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 150 (Polychromatic418967fa.accept_9_7_1_6_1_261 52 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 73 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 150 (accept_3_5 50 73 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 150 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 73 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 150
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 150 (accept_3_5 47 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 150 (Polychromatic418967fa.accept_19_8_16_17_1_6552 46 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 150 (Polychromatic418967fa.accept_16_13_9_6_1_2306 45 73 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 150 (accept_3_5 44 73 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 73 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 150
  (Polychromatic418967fa.accept_13_3_8_7_1_4135 42 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 150 (accept_3_5 41 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 150 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 73 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 150 (accept_3_5 38 73 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 150 (Polychromatic418967fa.accept_19_18_16_17_1_2626 37 73 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 150
  (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 150 (accept_3_5 35 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 150 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 150 (Polychromatic418967fa.accept_19_14_16_17_1_6565 33 73 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 150 (accept_3_5 32 73 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 73 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 150
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 150 (accept_3_5 29 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 150 (Polychromatic418967fa.accept_13_2_8_7_1_2424 28 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 73 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 150 (accept_3_5 26 73 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 150 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 73 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 150
  (Polychromatic418967fa.accept_22_2_7_18_1_6403 24 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 150 (accept_3_5 23 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 150 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 150 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 73 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 150 (accept_3_5 20 73 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 73 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 150
  (Polychromatic418967fa.accept_16_2_9_6_1_4441 18 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 150 (accept_3_5 17 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 150 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 73 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 150 (accept_3_5 14 73 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 150 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 73 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 150
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 150 (accept_3_5 11 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 150 (Polychromatic418967fa.accept_13_10_8_7_1_1074 10 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 150 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 73 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 150 (accept_3_5 8 73 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 73 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 150
  (Polychromatic418967fa.accept_14_6_3_10_1_3905 6 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 150 (accept_3_5 5 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  150 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 73 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 73 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 150 (accept_3_5 2 73 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 150 (Polychromatic418967fa.accept_13_1_8_7_1_1088 1 73 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  150))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 150 (allA_succ_of_accept 71
  72 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 71 72 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 72 150 2 35 36 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 69 72 150 3 23 24 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 72 150 2 34 36 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 72 150 (Polychromatic418967fa.accept_11_1_6_7_1_116 67 72 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 150 6 11 12 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 150
  (Polychromatic418967fa.accept_19_8_15_17_1_8060 65 72 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 72 150 2 32 36 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 72 150 3 21 24 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 72 150 2 31 36 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 72 150 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 72 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 150 6 10 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 150 (Polychromatic418967fa.accept_19_2_15_17_1_2614
  59 72 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72 150 2 29 36 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 72 150 3 19 24 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 72 150 2 28 36 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 72 150
  (Polychromatic418967fa.accept_7_6_2_3_1_107 55 72 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 72 150 6 9 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 72 150 (Polychromatic418967fa.accept_20_13_12_10_1_3619 53 72 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 72 150 2 26 36 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 72 150 3 17 24 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 72 150 2 25 36 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 150 (Polychromatic418967fa.accept_21_7_9_3_1_8059
  49 72 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 150 6 8 12 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 150
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 72 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 72 150 2 23 36 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 72 150 3 15 24 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 72 150 2 22 36 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 72 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 72 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 150 6 7 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 72 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 72 150 2 20 36 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 72 150 3 13 24 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 72 150 2 19 36 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 150
  (Polychromatic418967fa.accept_21_16_9_3_1_6436 37 72 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 150 6 6 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 72 150 (Polychromatic418967fa.accept_17_1_4_14_1_8058 35 72 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 150 2 17 36 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 72 150 3 11 24 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 72 150 2 16 36 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 72 150
  (Polychromatic418967fa.accept_19_12_15_17_1_3837 31 72 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 72 150 6 5 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 72 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 72 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 150 2 14 36 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 72 150 3 9 24 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 72 150 2 13 36 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 150
  (Polychromatic418967fa.accept_20_5_12_10_1_5072 25 72 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 72 150 6 4 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 72 150 (Polychromatic418967fa.accept_11_1_6_7_1_116 23 72 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 150 2 11 36 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 72 150 3 7 24 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 72 150 2 10 36 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 72 150 (Polychromatic418967fa.accept_7_5_2_3_1_106 19
  72 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 150 6 3 12 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 150
  (Polychromatic418967fa.accept_21_17_9_3_1_6437 17 72 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 72 150 2 8 36 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 72 150 3 5 24 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 72 150 2 7 36 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 72 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 72 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 150 6 2 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 150 (Polychromatic418967fa.accept_22_11_6_18_1_6402 11 72
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 150 2 5 36 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 72 150 3 3 24 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 72 150 2 4 36 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 150
  (Polychromatic418967fa.accept_17_7_4_14_1_2106 7 72 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 72 150 6 1 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 72 150 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 72 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 150 2 2 36 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 72 150 3 1 24 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 72 150 2 1 36 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 72 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  150)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 150 (allA_succ_of_accept 70
  71 150 (accept_3_4 70 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 71 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 71 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 68 71 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 150 (accept_3_4 67 71 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 71 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 66 71 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 65
  71 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 71 150 (accept_3_4 64 71
  150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 71 150
  (Polychromatic418967fa.accept_16_15_7_6_1_1453 63 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 71 150 (Polychromatic418967fa.accept_17_11_3_14_1_6736 62 71 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 150 (accept_3_4 61 71 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 71 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 71 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 150 (Polychromatic418967fa.accept_9_5_8_6_1_281 59
  71 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 71 150 (accept_3_4 58 71
  150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 71 150 (Polychromatic418967fa.accept_4_1_3_2_1_3
  57 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 71 150
  (Polychromatic418967fa.accept_9_2_8_6_1_79 56 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 71 150 (accept_3_4 55 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  71 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 71 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 71 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 71 150 (accept_3_4 52 71 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 71 150 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 71 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 71 150
  (Polychromatic418967fa.accept_9_5_8_6_1_281 50 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 71 150 (accept_3_4 49 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  71 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 71 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 71 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 71 150 (accept_3_4 46 71 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 71 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 71 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 71 150
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 71 150 (accept_3_4 43 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  71 150 (Polychromatic418967fa.accept_11_9_5_7_1_815 42 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 71 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 71 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 71 150 (accept_3_4 40 71 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 71 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 71 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 71 150
  (Polychromatic418967fa.accept_9_2_8_6_1_79 38 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 71 150 (accept_3_4 37 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  71 150 (Polychromatic418967fa.accept_17_2_3_14_1_8043 36 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 71 150 (Polychromatic418967fa.accept_13_9_6_7_1_551 35 71 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 71 150 (accept_3_4 34 71 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 71 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 71 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 71 150
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 71 150 (accept_3_4 31 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  71 150 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 71 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 71 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 71 150 (accept_3_4 28 71 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 71 150 (Polychromatic418967fa.accept_13_1_6_7_1_550 27 71 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 150
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 71 150 (accept_3_4 25 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  71 150 (Polychromatic418967fa.accept_19_5_14_17_1_6550 24 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 71 150 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 71 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 150 (accept_3_4 22 71 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 71 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 71 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 150
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 71 150 (accept_3_4 19 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  71 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 71 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 71 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 150 (accept_3_4 16 71 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 71 150 (Polychromatic418967fa.accept_16_15_7_6_1_1453 15 71 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 150
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 71 150 (accept_3_4 13 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  71 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 71 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 71 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 150 (accept_3_4 10 71 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 71 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 71 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 150
  (Polychromatic418967fa.accept_27_8_17_15_1_4070 8 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 71 150 (accept_3_4 7 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71
  150 (Polychromatic418967fa.accept_17_6_3_14_1_2078 6 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 71 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 71 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 150 (accept_3_4 4 71 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 71 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 71 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 150
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 71 150 (accept_3_4 1 71 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71
  150))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 150 (allA_succ_of_accept 69
  70 150 (Polychromatic418967fa.accept_11_3_4_7_1_114 69 70 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 70 150 2 34 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 70 150 (Polychromatic418967fa.accept_9_4_7_6_1_255 67 70 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 70 150 2 33 35 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 70 150 5 13 14 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 70 150 2 32 35 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 70 150
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 63 70 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 70 150 2 31 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 70 150 (Polychromatic418967fa.accept_19_4_13_17_1_5137 61 70 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 70 150 10 6 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 70 150 (accept_3_5 59 70 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 70 150 2 29 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 70 150 (Polychromatic418967fa.accept_9_3_7_6_1_76 57 70 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 70 150 2 28 35 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 70 150 5 11 14 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 70 150 2 27 35 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 70 150 (accept_3_5 53 70 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 70 150 2 26 35 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 70 150
  (Polychromatic418967fa.accept_12_3_10_6_1_442 51 70 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 70 150 10 5 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 70 150 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 70 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 70 150 2 24 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 70 150 (accept_3_5 47 70 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 70 150 2 23 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 70 150 5 9 14 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 70 150 2 22 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 70 150 (Polychromatic418967fa.accept_21_1_7_3_1_6450 43 70 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 70 150 2 21 35 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 70 150 (accept_3_5 41
  70 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70 150 10 4 7 15 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 70 150
  (Polychromatic418967fa.accept_9_3_7_6_1_76 39 70 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 70 150 2 19 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 70 150 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 70 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 70 150 2 18 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 70 150 5 7 14 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 70 150 2 17 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 70 150 (Polychromatic418967fa.accept_12_9_10_6_1_872
  33 70 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 70 150 2 16 35 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 70 150
  (Polychromatic418967fa.accept_9_4_7_6_1_255 31 70 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 70 150 10 3 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 70 150 (accept_3_5 29 70 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70
  150 2 14 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  70 150 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 70 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 70 150 2 13 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 25 70 150 5 5 14 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 70 150 2 12 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 70 150 (accept_3_5 23 70 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 70 150 2 11 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 70 150 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 70 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 70 150 10 2 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 70 150 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 70 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 70 150 2 9 35 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 70 150 (accept_3_5 17 70 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 70 150 2 8 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 70 150 5 3 14 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 70 150 2 7 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 70 150 (Polychromatic418967fa.accept_9_4_7_6_1_255 13
  70 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 70 150 2 6 35 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 70 150 (accept_3_5 11
  70 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 150 10 1 7 15 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 70 150
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 70 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 70 150 2 4 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 70 150 (Polychromatic418967fa.accept_19_7_13_17_1_8041 7 70 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 70 150 2 3 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 70 150 5 1 14 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 70 150 2 2 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 70 150 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 70 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 150 2 1 35 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 150
  (Polychromatic418967fa.accept_9_1_7_6_1_75 1 70 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 150)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 150
  (allA_succ_of_accept 68 69 150 (Polychromatic418967fa.accept_12_8_9_6_1_127 68 69 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 69 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 69 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 69 150 3 22 23 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 69 150
  (Polychromatic418967fa.accept_7_2_6_3_1_100 65 69 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 69 150 (Polychromatic418967fa.accept_12_4_9_6_1_440 64 69 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 69 150 3 21 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 69 150 (Polychromatic418967fa.accept_12_2_9_6_1_439 62
  69 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 150
  (Polychromatic418967fa.accept_13_9_4_7_1_1694 61 69 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 69 150 3 20 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 69 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 69 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 69 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 69 150 3 19 23 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 69 150
  (Polychromatic418967fa.accept_12_8_9_6_1_127 56 69 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 69 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 69 150 3 18 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 69 150 (Polychromatic418967fa.accept_7_4_6_3_1_271 53
  69 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 150
  (Polychromatic418967fa.accept_12_4_9_6_1_440 52 69 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 69 150 3 17 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 69 150 (Polychromatic418967fa.accept_12_2_9_6_1_439 50 69 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 150 (Polychromatic418967fa.accept_13_10_4_7_1_2465 49 69
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 69 150 3 16 23 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 69 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 69 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 69 150 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 69 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 69 150 3 15 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 69 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 44
  69 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 69 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 69 150 3 14 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 69 150 (Polychromatic418967fa.accept_18_5_15_6_1_3999 41 69 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 150 (Polychromatic418967fa.accept_12_4_9_6_1_440 40 69 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 69 150 3 13 23 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 69 150
  (Polychromatic418967fa.accept_12_2_9_6_1_439 38 69 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 69 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 69 150 3 12 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 69 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 35
  69 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 150
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 34 69 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 69 150 3 11 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 69 150 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 69 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 69 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 69 150 3 10 23 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 150
  (Polychromatic418967fa.accept_13_3_4_7_1_1711 29 69 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 150 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 69 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 69 150 3 9 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 69 150 (Polychromatic418967fa.accept_11_4_3_7_1_828 26 69 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 150
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 69 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 69 150 3 8 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 69 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 69 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 150 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 69
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 150 3 7 23 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 150
  (Polychromatic418967fa.accept_12_8_9_6_1_127 20 69 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 69 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 69 150 3 6 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 69 150 (Polychromatic418967fa.accept_14_3_13_10_1_761 17 69 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 150
  (Polychromatic418967fa.accept_7_2_6_3_1_100 16 69 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 69 150 3 5 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 69 150 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 69 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 150 (Polychromatic418967fa.accept_17_13_1_14_1_1149 13 69
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 150 3 4 23 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 69 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 150 (Polychromatic418967fa.accept_11_10_3_7_1_2564 10 69 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 69 150 3 3 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 69 150 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 69 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 69 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 69 150 3 2 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 69 150 (Polychromatic418967fa.accept_18_5_15_6_1_3999 5 69 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 150 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 69 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 150 3 1 23 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 150
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 69 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 150 (Polychromatic418967fa.accept_16_1_5_6_1_4435 1 69 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 69 150)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 68 150 (allA_succ_of_accept 67 68 150 (accept_3_4 67 68 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 68 150 2 33 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 68 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 65 68 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 68 150 2 32 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 68 150 (Polychromatic418967fa.accept_12_3_8_6_1_895 63
  68 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 68 150 2 31 34 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 68 150 (accept_3_4 61
  68 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 68 150 2 30 34 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 68 150
  (Polychromatic418967fa.accept_16_11_4_6_1_4422 59 68 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 68 150 2 29 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 68 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 68 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 68 150 2 28 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 68 150 (accept_3_4 55 68 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 68 150 2 27 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 68 150 (Polychromatic418967fa.accept_9_8_5_6_1_538 53 68 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 68 150 2 26 34 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 68 150
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 68 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 68 150 2 25 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 68 150 (accept_3_4 49 68 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 68
  150 2 24 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  68 150 (Polychromatic418967fa.accept_9_2_5_6_1_536 47 68 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 68 150 2 23 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 68 150 (Polychromatic418967fa.accept_12_9_8_6_1_466 45 68 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 68 150 2 22 34 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 68 150 (accept_3_4 43 68 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68 150 2 21 34 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 68 150
  (Polychromatic418967fa.accept_29_12_10_5_1_8057 41 68 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 68 150 2 20 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 68 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 68 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 68 150 2 19 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 68 150 (accept_3_4 37 68 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68 150 2 18 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 68 150 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 68 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 68 150 2 17 34 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 68 150
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 68 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 68 150 2 16 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 68 150 (accept_3_4 31 68 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68
  150 2 15 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  68 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 68 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 68 150 2 14 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 68 150 (Polychromatic418967fa.accept_12_3_8_6_1_895 27 68 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 68 150 2 13 34 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 68 150 (accept_3_4 25 68 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68 150 2 12 34 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 68 150
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 68 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 68 150 2 11 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 68 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 68 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 68 150 2 10 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 68 150 (accept_3_4 19 68 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68 150 2 9 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 68 150 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 68 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 68 150 2 8 34 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 68 150
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 68 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 68 150 2 7 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 68 150 (accept_3_4 13 68 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68
  150 2 6 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  68 150 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 68 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 68 150 2 5 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 68 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 68 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 68 150 2 4 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 68 150 (accept_3_4 7 68 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 150 2 3 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 68 150 (Polychromatic418967fa.accept_14_5_12_10_1_2985 5 68 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 68 150 2 2 34 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 68 150
  (Polychromatic418967fa.accept_9_3_5_6_1_253 3 68 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 68 150 2 1 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 68 150 (accept_3_4 1 68 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  150)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 150 (allA_succ_of_accept 66 67
  150 (Polychromatic418967fa.accept_9_3_4_6_1_252 66 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 150 (accept_3_5 65 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 150 (Polychromatic418967fa.accept_14_7_11_10_1_2155 63 67 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 150 (accept_3_5 62 67 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 67 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 150
  (Polychromatic418967fa.accept_13_8_2_7_1_2452 60 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 150 (accept_3_5 59 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 150 (Polychromatic418967fa.accept_19_1_10_17_1_5188 58 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 67 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 150 (accept_3_5 56 67 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 150 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 67 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 150
  (Polychromatic418967fa.accept_21_12_4_3_1_4924 54 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 150 (accept_3_5 53 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 150 (Polychromatic418967fa.accept_9_7_4_6_1_273 52 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 150 (Polychromatic418967fa.accept_20_11_7_10_1_8056 51 67 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 150 (accept_3_5 50 67 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 67 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 150
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 150 (accept_3_5 47 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 67 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 150 (accept_3_5 44 67 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 67 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 150
  (Polychromatic418967fa.accept_17_8_16_14_1_4261 42 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 150 (accept_3_5 41 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 150 (Polychromatic418967fa.accept_19_2_10_17_1_3876 40 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 150 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 67 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 150 (accept_3_5 38 67 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 67 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 150
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 150 (accept_3_5 35 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 150 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 67 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 150 (accept_3_5 32 67 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 150 (Polychromatic418967fa.accept_13_5_2_7_1_2414 31 67 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 150
  (Polychromatic418967fa.accept_9_3_4_6_1_252 30 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 150 (accept_3_5 29 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 150 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 67 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 150 (accept_3_5 26 67 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 67 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 150
  (Polychromatic418967fa.accept_22_2_1_18_1_8055 24 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 150 (accept_3_5 23 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 67 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 150 (accept_3_5 20 67 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 67 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 150
  (Polychromatic418967fa.accept_13_5_2_7_1_2414 18 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 150 (accept_3_5 17 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 150 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 67 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 150 (accept_3_5 14 67 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 67 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 150
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 150 (accept_3_5 11 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 67 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 150 (accept_3_5 8 67 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 150 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 67 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 150
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 150 (accept_3_5 5 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  150 (Polychromatic418967fa.accept_16_4_3_6_1_6805 4 67 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 150 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 67 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 150 (accept_3_5 2 67 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 67 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  150))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 150 (allA_succ_of_accept 65 66
  150 (Polychromatic418967fa.accept_9_2_3_6_1_88 65 66 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 66 150 2 32 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 66 150 3 21 22 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 66 150 2 31 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 66 150 (Polychromatic418967fa.accept_9_7_3_6_1_270 61 66 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 150 6 10 11 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 150 (Polychromatic418967fa.accept_9_5_3_6_1_269 59
  66 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 150 2 29 33 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 66 150 3 19 22 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 66 150 2 28 33 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 66 150
  (Polychromatic418967fa.accept_9_1_3_6_1_70 55 66 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 66 150 6 9 11 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 66 150 (Polychromatic418967fa.accept_9_8_3_6_1_533 53 66 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66 150 2 26 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 66 150 3 17 22 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 66 150 2 25 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 66 150 (Polychromatic418967fa.accept_9_4_3_6_1_532 49
  66 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 150 6 8 11 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 150
  (Polychromatic418967fa.accept_9_2_3_6_1_88 47 66 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 66 150 2 23 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 66 150 3 15 22 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 66 150 2 22 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 66 150 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 66 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 150 6 7 11 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 150 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 66 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 150 2 20 33 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 66 150 3 13 22 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 66 150 2 19 33 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 150
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 66 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 150 6 6 11 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 66 150 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 66 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 150 2 17 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 66 150 3 11 22 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 66 150 2 16 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 150 (Polychromatic418967fa.accept_9_4_3_6_1_532 31
  66 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 150 6 5 11 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 150
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 66 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 66 150 2 14 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 66 150 3 9 22 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 66 150 2 13 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 66 150 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 66 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 150 6 4 11 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 150 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 66 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 150 2 11 33 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 66 150 3 7 22 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 66 150 2 10 33 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 150
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 66 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 150 6 3 11 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 150 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 66 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 150 2 8 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 66 150 3 5 22 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 66 150 2 7 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 150 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 66 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 150 6 2 11 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 150
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 66 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 66 150 2 5 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 66 150 3 3 22 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 66 150 2 4 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 66 150 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 66 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 150 6 1 11 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 150 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 66 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 150 2 2 33 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 66 150 3 1 22 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 66 150 2 1 33 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 150
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 66 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 66 150)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 150
  (allA_succ_of_accept 64 65 150 (accept_3_4 64 65 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  65 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 65 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 65 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 62 65 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 150 (accept_3_4 61 65 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 65 150 5 12 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 65 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 65 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 150 (accept_3_4 58 65 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 57
  65 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 65 150
  (Polychromatic418967fa.accept_20_16_5_10_1_6487 56 65 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 65 150 5 11 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 65 150 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 65 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 150 (Polychromatic418967fa.accept_9_8_2_6_1_875 53 65 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 150 (accept_3_4 52 65 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 51
  65 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 65 150 5 10 13 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 65 150 (accept_3_4 49
  65 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 150
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 65 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 65 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 65 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 150 (accept_3_4 46 65 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 65 150 5 9 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 65 150 (Polychromatic418967fa.accept_9_8_2_6_1_875 44 65 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 150 (accept_3_4 43 65 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 150 (Polychromatic418967fa.accept_19_4_8_17_1_8054 42 65 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 150
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 65 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 65 150 5 8 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 65 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 65 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 150 (Polychromatic418967fa.accept_20_18_5_10_1_3533 38 65
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 150 (accept_3_4 37 65 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 36
  65 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 65 150 5 7 13 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 65 150 (accept_3_4 34
  65 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 150
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 65 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 65 150 (Polychromatic418967fa.accept_9_5_2_6_1_265 32 65 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 150 (accept_3_4 31 65 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 65 150 5 6 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 65 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 65 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 150 (accept_3_4 28 65 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 65 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 150
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 65 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 65 150 5 5 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 65 150 (Polychromatic418967fa.accept_20_4_5_10_1_2308 24 65 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 65 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 150 (accept_3_4 22 65 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 21
  65 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 65 150 5 4 13 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 65 150 (accept_3_4 19
  65 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 150
  (Polychromatic418967fa.accept_16_2_1_6_1_2342 18 65 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 65 150 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 65 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 150 (accept_3_4 16 65 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 65 150 5 3 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 65 150 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 65 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 150 (accept_3_4 13 65 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 150 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 65 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 65 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 65 150 5 2 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 65 150 (Polychromatic418967fa.accept_19_9_8_17_1_8053 9 65 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 65 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 150 (accept_3_4 7 65 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 6
  65 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 65 150 5 1 13 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 65 150 (accept_3_4 4 65
  150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 150 (Polychromatic418967fa.accept_4_3_1_2_1_62
  3 65 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 150
  (Polychromatic418967fa.accept_16_2_1_6_1_2342 2 65 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 65 150 (accept_3_4 1 65 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  150))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 150 (allA_succ_of_accept 63 64 150
  (Polychromatic418967fa.accept_12_3_4_6_1_434 63 64 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 64 150 2 31 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 64 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 64 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 64 150 2 30 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 64 150 (accept_3_5 59 64 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 64 150 2 29 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 64 150 (Polychromatic418967fa.accept_9_3_1_6_1_86 57 64 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 64 150 2 28 32 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 64 150
  (Polychromatic418967fa.accept_17_4_13_14_1_1139 55 64 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 64 150 2 27 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 64 150 (accept_3_5 53 64 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 64
  150 2 26 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  64 150 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 64 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 64 150 2 25 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 64 150 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 64 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 64 150 2 24 32 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 64 150 (accept_3_5 47 64 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 64 150 2 23 32 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 64 150
  (Polychromatic418967fa.accept_12_9_4_6_1_460 45 64 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 64 150 2 22 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 64 150 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 64 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 64 150 2 21 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 64 150 (accept_3_5 41 64 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 64 150 2 20 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 64 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 64 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 64 150 2 19 32 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 64 150
  (Polychromatic418967fa.accept_7_2_1_3_1_102 37 64 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 64 150 2 18 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 64 150 (accept_3_5 35 64 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 64
  150 2 17 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  64 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 64 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 64 150 2 16 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 64 150 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 64 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 64 150 2 15 32 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 64 150 (accept_3_5 29 64 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64 150 2 14 32 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 64 150
  (Polychromatic418967fa.accept_11_5_9_7_1_411 27 64 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 64 150 2 13 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 64 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 64 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 64 150 2 12 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 64 150 (accept_3_5 23 64 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64 150 2 11 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 64 150 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 64 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 64 150 2 10 32 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 64 150
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 64 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 64 150 2 9 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 64 150 (accept_3_5 17 64 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64
  150 2 8 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  64 150 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 64 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 64 150 2 7 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 64 150 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 64 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 150 2 6 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 150 (accept_3_5 11 64 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64 150 2 5 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 64 150 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 64 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 64 150 2 4 32 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 64 150
  (Polychromatic418967fa.accept_9_7_1_6_1_261 7 64 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 64 150 2 3 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 64 150 (accept_3_5 5 64 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 150
  2 2 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 64
  150 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 64 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 64 150 2 1 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 64 150 (Polychromatic418967fa.accept_17_1_13_14_1_478 1 64 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 64 150))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 63 150 (allA_succ_of_accept 62 63 150 (Polychromatic418967fa.accept_12_2_3_6_1_112 62 63 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 63 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 61 63 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 63 150 3 20 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 63 150 (Polychromatic418967fa.accept_11_4_8_7_1_819 59 63 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 150 (Polychromatic418967fa.accept_12_10_3_6_1_882 58 63 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 63 150 3 19 21 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 63 150
  (Polychromatic418967fa.accept_12_8_3_6_1_909 56 63 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 150 (Polychromatic418967fa.accept_13_3_11_7_1_2488 55 63 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 63 150 3 18 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 63 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 63
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 150
  (Polychromatic418967fa.accept_12_4_3_6_1_879 52 63 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 63 150 3 17 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 63 150 (Polychromatic418967fa.accept_12_2_3_6_1_112 50 63 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 63 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 63 150 3 16 21 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 63 150
  (Polychromatic418967fa.accept_19_9_6_17_1_3880 47 63 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 63 150 (Polychromatic418967fa.accept_12_10_3_6_1_882 46 63 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 63 150 3 15 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 63 150 (Polychromatic418967fa.accept_12_8_3_6_1_909 44
  63 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 150
  (Polychromatic418967fa.accept_13_4_11_7_1_558 43 63 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 63 150 3 14 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 63 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 63 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 150 (Polychromatic418967fa.accept_12_4_3_6_1_879 40 63 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 63 150 3 13 21 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 63 150
  (Polychromatic418967fa.accept_12_2_3_6_1_112 38 63 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 63 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 63 150 3 12 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 63 150 (Polychromatic418967fa.accept_13_9_11_7_1_1077
  35 63 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 150
  (Polychromatic418967fa.accept_12_10_3_6_1_882 34 63 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 63 150 3 11 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 63 150 (Polychromatic418967fa.accept_12_8_3_6_1_909 32 63 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 150 (Polychromatic418967fa.accept_13_5_11_7_1_559 31 63 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 63 150 3 10 21 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 63 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 63 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 63 150 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 63 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 63 150 3 9 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 63 150 (Polychromatic418967fa.accept_11_4_8_7_1_819 26 63 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 63 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 63 150 3 8 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 63 150 (Polychromatic418967fa.accept_16_7_15_6_1_1428 23 63 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 150 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 63 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 150 3 7 21 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 150
  (Polychromatic418967fa.accept_12_8_3_6_1_909 20 63 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 150 (Polychromatic418967fa.accept_18_1_9_6_1_6630 19 63 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 63 150 3 6 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 63 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 63 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 150
  (Polychromatic418967fa.accept_12_4_3_6_1_879 16 63 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 63 150 3 5 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 63 150 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 63 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 63 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 63 150 3 4 21 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 63 150
  (Polychromatic418967fa.accept_14_11_7_10_1_4852 11 63 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 63 150 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 63 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 150 3 3 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 150 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 63 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 150
  (Polychromatic418967fa.accept_16_7_15_6_1_1428 7 63 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 63 150 3 2 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 63 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 63 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 150 (Polychromatic418967fa.accept_11_4_8_7_1_819 4 63 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 63 150 3 1 21 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 63 150
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 63 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 63 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 63 150)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 62 150 (allA_succ_of_accept 61 62 150 (accept_3_4 61 62 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 62 150 2 30 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 62 150 (Polychromatic418967fa.accept_9_5_8_6_1_281 59 62 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 62 150 2 29 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 62 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 57
  62 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 150 2 28 31 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 150 (accept_3_4 55
  62 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 150 2 27 31 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 150
  (Polychromatic418967fa.accept_7_4_6_3_1_271 53 62 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 62 150 2 26 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 62 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 62 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 62 150 2 25 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 62 150 (accept_3_4 49 62 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 62 150 2 24 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 62 150 (Polychromatic418967fa.accept_9_2_8_6_1_79 47 62 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 62 150 2 23 31 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 62 150
  (Polychromatic418967fa.accept_12_9_2_6_1_455 45 62 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 62 150 2 22 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 62 150 (accept_3_4 43 62 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 62
  150 2 21 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  62 150 (Polychromatic418967fa.accept_9_5_8_6_1_281 41 62 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 62 150 2 20 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 62 150 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 62 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 62 150 2 19 31 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 62 150 (accept_3_4 37 62 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 62 150 2 18 31 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 62 150
  (Polychromatic418967fa.accept_20_15_2_10_1_8052 35 62 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 62 150 2 17 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 62 150 (Polychromatic418967fa.accept_12_9_2_6_1_455 33 62 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 62 150 2 16 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 62 150 (accept_3_4 31 62 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 62 150 2 15 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 62 150 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 62 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 62 150 2 14 31 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 62 150
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 62 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 62 150 2 13 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 62 150 (accept_3_4 25 62 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62
  150 2 12 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  62 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 62 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 62 150 2 11 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 62 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 62 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 62 150 2 10 31 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 62 150 (accept_3_4 19 62 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 62 150 2 9 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 62 150 (Polychromatic418967fa.accept_13_4_10_7_1_1701
  17 62 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 150 2 8 31 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 150
  (Polychromatic418967fa.accept_12_3_2_6_1_138 15 62 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 62 150 2 7 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 62 150 (accept_3_4 13 62 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62
  150 2 6 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  62 150 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 62 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 62 150 2 5 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 62 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 62 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 150 2 4 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 150 (accept_3_4 7 62 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 62 150 2 3 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 62 150 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 62 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 150 2 2 31 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 150
  (Polychromatic418967fa.accept_9_3_8_6_1_80 3 62 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 62 150 2 1 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 62 150 (accept_3_4 1 62 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  150)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 150 (allA_succ_of_accept 60 61 150
  (Polychromatic418967fa.accept_13_8_9_7_1_530 60 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 150 (accept_3_5 59 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 61 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 150 (accept_3_5 56 61 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 61 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 150
  (Polychromatic418967fa.accept_13_2_9_7_1_164 54 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 150 (accept_3_5 53 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 150 (Polychromatic418967fa.accept_16_4_13_6_1_4417 52 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 61 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 150 (accept_3_5 50 61 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 150 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 61 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 150
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 150 (accept_3_5 47 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 150 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 150 (Polychromatic418967fa.accept_11_1_6_7_1_116 45 61 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 150 (accept_3_5 44 61 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 61 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 150
  (Polychromatic418967fa.accept_13_3_9_7_1_1730 42 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 150 (accept_3_5 41 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 150 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 61 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 150 (accept_3_5 38 61 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 61 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 150
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 150 (accept_3_5 35 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 150 (Polychromatic418967fa.accept_11_1_6_7_1_116 34 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 150 (Polychromatic418967fa.accept_20_13_1_10_1_8051 33 61 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 150 (accept_3_5 32 61 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 61 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 150
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 150 (accept_3_5 29 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 150 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 61 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 150 (accept_3_5 26 61 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 150 (Polychromatic418967fa.accept_16_9_13_6_1_2334 25 61 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 150
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 24 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 150 (accept_3_5 23 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 150 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 61 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 150 (accept_3_5 20 61 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 61 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 150
  (Polychromatic418967fa.accept_17_1_10_14_1_1173 18 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 150 (accept_3_5 17 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 61 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 150 (accept_3_5 14 61 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 150 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 61 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 150
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 150 (accept_3_5 11 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 150 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 61 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 150 (accept_3_5 8 61 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 61 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 150
  (Polychromatic418967fa.accept_13_6_9_7_1_2430 6 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 150 (accept_3_5 5 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  150 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 61 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 61 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 150 (accept_3_5 2 61 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 61 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 150)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 150 (allA_succ_of_accept 59 60 150 (Polychromatic418967fa.accept_19_2_3_17_1_5146 59 60 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 60 150 2 29 30 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 60 150 3 19 20 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 60 150 2 28 30 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 60 150 5 11 12 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 60 150 6 9 10 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 150
  (Polychromatic418967fa.accept_11_9_5_7_1_815 53 60 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 60 150 2 26 30 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 51 60 150 3 17 20 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 60 150 10 5 6 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 150 (Polychromatic418967fa.accept_13_10_8_7_1_1074 49 60 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 150 6 8 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 150 (Polychromatic418967fa.accept_21_5_18_3_1_4908 47 60 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 150 2 23 30 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 60 150 15 3 4 10 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 60 150 2 22 30 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 150
  (Polychromatic418967fa.accept_7_1_4_3_1_21 43 60 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 60 150 6 7 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 60 150 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 60 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 150 10 4 6 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 60 150 3 13 20 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 60 150 2 19 30 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 150 (Polychromatic418967fa.accept_21_16_18_3_1_8050 37 60
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 150 6 6 10 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 60 150 5 7 12 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 60 150 2 17 30 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 60 150 3 11 20 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 60 150 2 16 30 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 150
  (Polychromatic418967fa.accept_11_9_5_7_1_815 31 60 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 150 30 1 2 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 60 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 60 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60 150 2 14 30 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 60 150 3 9 20 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 60 150 2 13 30 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 60 150 5 5 12 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 60 150 6 4 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 150 (Polychromatic418967fa.accept_13_10_8_7_1_1074
  23 60 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 150 2 11 30 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 60 150 3 7 20 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 60 150 10 2 6 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 150
  (Polychromatic418967fa.accept_21_19_18_3_1_4910 19 60 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 60 150 6 3 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 60 150 (Polychromatic418967fa.accept_21_17_18_3_1_4909 17 60 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 150 2 8 30 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 60 150 15 1 4 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 60 150 2 7 30 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 150 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 60 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 150 6 2 10 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 150
  (Polychromatic418967fa.accept_21_11_18_3_1_4862 11 60 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 60 150 10 1 6 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 60 150 3 3 20 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 60 150 2 4 30 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 60 150 (Polychromatic418967fa.accept_14_7_4_10_1_1351 7 60 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 150 6 1 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 60 150 5 1 12 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 60 150 2 2 30 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 60 150 3 1 20 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 60 150 2 1 30 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 60 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  150)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 150 (allA_succ_of_accept 58 59 150
  (accept_3_4 58 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 150 (Polychromatic418967fa.accept_9_2_5_6_1_536 56 59 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 150 (accept_3_4 55 59 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 150 (Polychromatic418967fa.accept_19_16_2_17_1_8049 54 59 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 150 (accept_3_4 52 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 150 (Polychromatic418967fa.accept_16_3_11_6_1_4467 51 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 150 (Polychromatic418967fa.accept_16_2_11_6_1_737 50 59 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 150 (accept_3_4 49 59 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 59 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 150
  (Polychromatic418967fa.accept_9_2_5_6_1_536 47 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 150 (accept_3_4 46 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 150 (Polychromatic418967fa.accept_9_8_5_6_1_538 44 59 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 150 (accept_3_4 43 59 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 150 (Polychromatic418967fa.accept_19_4_2_17_1_3870 42 59 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 150 (accept_3_4 40 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 150 (Polychromatic418967fa.accept_9_2_5_6_1_536 38 59 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 150 (accept_3_4 37 59 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 150 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 59 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 150
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 150 (accept_3_4 34 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 150 (Polychromatic418967fa.accept_29_3_1_5_1_8048 32 59 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 150 (accept_3_4 31 59 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 59 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 150 (accept_3_4 28 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 150 (Polychromatic418967fa.accept_14_13_3_10_1_2159 27 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 150 (Polychromatic418967fa.accept_9_8_5_6_1_538 26 59 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 150 (accept_3_4 25 59 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 150 (Polychromatic418967fa.accept_17_7_8_14_1_6720 24 59 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 150
  (Polychromatic418967fa.accept_17_6_8_14_1_6706 23 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 150 (accept_3_4 22 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 150 (Polychromatic418967fa.accept_9_2_5_6_1_536 20 59 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 150 (accept_3_4 19 59 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 150 (Polychromatic418967fa.accept_16_2_11_6_1_737 18 59 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 150 (accept_3_4 16 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 150 (Polychromatic418967fa.accept_18_15_5_6_1_5293 15 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 150 (Polychromatic418967fa.accept_11_3_4_7_1_114 14 59 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 150 (accept_3_4 13 59 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 59 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 150
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 150 (accept_3_4 10 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 59 150 (Polychromatic418967fa.accept_9_8_5_6_1_538 8 59 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 150 (accept_3_4 7 59 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 59 150 (Polychromatic418967fa.accept_14_6_3_10_1_3905 6 59 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 59
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 150 (accept_3_4 4 59 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 3
  59 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 150
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 59 150 (accept_3_4 1 59 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59
  150))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 150 (allA_succ_of_accept 57 58 150
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 58 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 58 150 2 28 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 58 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 58 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 58 150 2 27 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 58 150 (accept_3_5 53 58 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58 150 2 26 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 58 150 (Polychromatic418967fa.accept_12_3_10_6_1_442 51 58 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 58 150 2 25 29 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 58 150
  (Polychromatic418967fa.accept_21_7_16_3_1_1058 49 58 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 58 150 2 24 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 58 150 (accept_3_5 47 58 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 58
  150 2 23 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  58 150 (Polychromatic418967fa.accept_12_9_10_6_1_872 45 58 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 58 150 2 22 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 58 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 58 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 58 150 2 21 29 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 58 150 (accept_3_5 41 58 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 58 150 2 20 29 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 58 150
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 58 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 58 150 2 19 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 58 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 58 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 58 150 2 18 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 58 150 (accept_3_5 35 58 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58 150 2 17 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 58 150 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 58 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 58 150 2 16 29 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 58 150
  (Polychromatic418967fa.accept_21_10_16_3_1_8047 31 58 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 58 150 2 15 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 58 150 (accept_3_5 29 58 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 58
  150 2 14 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  58 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 58 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 58 150 2 13 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 58 150 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 58 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 58 150 2 12 29 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 58 150 (accept_3_5 23 58 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58 150 2 11 29 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 58 150
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 58 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 58 150 2 10 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 58 150 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 58 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 58 150 2 9 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 58 150 (accept_3_5 17 58 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 58 150 2 8 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 58 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 58 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 58 150 2 7 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 58 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 13
  58 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 150 2 6 29 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 150 (accept_3_5 11
  58 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 150 2 5 29 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 58 150
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 58 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 58 150 2 4 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 58 150 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 58 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 150 2 3 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 150 (accept_3_5 5 58 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 58 150 2 2 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 58 150 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 58 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 150 2 1 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 58
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  150)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 150 (allA_succ_of_accept 56 57 150
  (Polychromatic418967fa.accept_9_2_3_6_1_88 56 57 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 57 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 57 150 3 18 19 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 57 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 53
  57 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 150
  (Polychromatic418967fa.accept_9_7_3_6_1_270 52 57 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 57 150 3 17 19 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 57 150 (Polychromatic418967fa.accept_9_5_3_6_1_269 50 57 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 150 (Polychromatic418967fa.accept_9_4_3_6_1_532 49 57 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 57 150 3 16 19 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 57 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 57 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 57 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 57 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 57 150 3 15 19 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 57 150 (Polychromatic418967fa.accept_7_2_1_3_1_102 44
  57 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 57 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 57 150 3 14 19 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 57 150 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 57 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 57 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 150 3 13 19 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 150
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 57 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 150 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 57 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 150 3 12 19 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 35
  57 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 150
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 57 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 57 150 3 11 19 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 57 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 57 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 57 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 150 3 10 19 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 150
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 57 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 150 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 57 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 150 3 9 19 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 57 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 150
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 57 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 57 150 3 8 19 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 57 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 57 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 150 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 57 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 150 3 7 19 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 150
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 57 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 57 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 150 3 6 19 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 150 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 57 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 150
  (Polychromatic418967fa.accept_7_2_1_3_1_102 16 57 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 57 150 3 5 19 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 57 150 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 57 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 150 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 57 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 150 3 4 19 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 57 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 150 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 57 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 150 3 3 19 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 150 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 57 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 57 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 57 150 3 2 19 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 57 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 57 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 57 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 150 3 1 19 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 150
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 57 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 150 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 57 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 57 150))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  56 150 (allA_succ_of_accept 55 56 150 (accept_3_4 55 56 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  54 56 150 2 27 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 56 150 (Polychromatic418967fa.accept_9_8_2_6_1_875 53 56 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 150 2 26 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 150 (Polychromatic418967fa.accept_12_3_8_6_1_895 51
  56 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 56 150 2 25 28 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 56 150 (accept_3_4 49
  56 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 56 150 2 24 28 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 56 150
  (Polychromatic418967fa.accept_31_16_25_26_1_8046 47 56 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 56 150 2 23 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 56 150 (Polychromatic418967fa.accept_12_9_8_6_1_466 45 56 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 56 150 2 22 28 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 56 150 (accept_3_4 43 56 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 150 2 21 28 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 56 150
  (Polychromatic418967fa.accept_9_5_2_6_1_265 41 56 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 56 150 2 20 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 56 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 56 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 56 150 2 19 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 56 150 (accept_3_4 37 56 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56 150 2 18 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 56 150 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 56 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 56 150 2 17 28 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 56 150
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 56 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 56 150 2 16 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 56 150 (accept_3_4 31 56 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56
  150 2 15 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  56 150 (Polychromatic418967fa.accept_13_3_4_7_1_1711 29 56 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 56 150 2 14 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 56 150 (Polychromatic418967fa.accept_12_3_8_6_1_895 27 56 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 150 2 13 28 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 150 (accept_3_4 25 56 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 150 2 12 28 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 56 150
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 56 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 56 150 2 11 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 56 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 56 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 56 150 2 10 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 56 150 (accept_3_4 19 56 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56 150 2 9 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 56 150 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 56 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 56 150 2 8 28 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 56 150
  (Polychromatic418967fa.accept_12_3_8_6_1_895 15 56 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 56 150 2 7 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 56 150 (accept_3_4 13 56 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56
  150 2 6 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  56 150 (Polychromatic418967fa.accept_13_11_4_7_1_2419 11 56 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 56 150 2 5 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 56 150 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 56 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 56 150 2 4 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 56 150 (accept_3_4 7 56 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 150 2 3 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 56 150 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 56 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 56 150 2 2 28 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 56 150
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 56 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 56 150 2 1 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 56 150 (accept_3_4 1 56 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56
  150)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 150 (allA_succ_of_accept 54 55 150
  (Polychromatic418967fa.accept_20_14_15_10_1_3554 54 55 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 55 150 (accept_3_5 53 55 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 55 150 (Polychromatic418967fa.accept_9_7_1_6_1_261 52 55 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 55 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 55 150 5 10 11 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 55 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 55 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 150 (Polychromatic418967fa.accept_9_3_1_6_1_86 48 55 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 150 (accept_3_5 47 55 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 150 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 55 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 55 150 5 9 11 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 55 150 (accept_3_5 44 55 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 150 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 55 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 150
  (Polychromatic418967fa.accept_20_2_15_10_1_5036 42 55 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 150 (accept_3_5 41 55 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 55
  150 5 8 11 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  55 150 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 55 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 55 150 (accept_3_5 38 55 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 55 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 55 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 150 (Polychromatic418967fa.accept_13_10_3_7_1_2517 36 55
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 55 150 5 7 11 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 55 150
  (Polychromatic418967fa.accept_9_7_1_6_1_261 34 55 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 55 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 55 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 150 (accept_3_5 32 55 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 55 150 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 55 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 55 150 5 6 11 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 55 150 (accept_3_5 29 55 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 150 (Polychromatic418967fa.accept_20_8_15_10_1_8045 28 55 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 150
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 55 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 150 (accept_3_5 26 55 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 55
  150 5 5 11 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  55 150 (Polychromatic418967fa.accept_13_11_3_7_1_2513 24 55 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 55 150 (accept_3_5 23 55 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 55 150 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 55 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 55 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 55 150 5 4 11 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 55 150
  (Polychromatic418967fa.accept_20_19_15_10_1_8044 19 55 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 55 150 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 55 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 150 (accept_3_5 17 55 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 55 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 55 150 5 3 11 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 55 150 (accept_3_5 14 55 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 55 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 150
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 55 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 150 (accept_3_5 11 55 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 55
  150 5 2 11 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  55 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 55 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 150 (accept_3_5 8 55 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  150 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 55 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 55 150 (Polychromatic418967fa.accept_20_6_15_10_1_3555 6 55 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 55 150 5 1 11 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 55 150 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 55 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 150
  (Polychromatic418967fa.accept_9_3_1_6_1_86 3 55 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 55 150 (accept_3_5 2 55 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55
  150 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 55 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 55 150))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 150 (allA_succ_of_accept 53 54
  150 (Polychromatic418967fa.accept_17_2_3_14_1_8043 53 54 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 54 150 2 26 27 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 51 54 150 3 17 18 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 54 150 2 25 27 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 54 150 (Polychromatic418967fa.accept_17_15_3_14_1_4230 49 54 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 150 6 8 9 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 150
  (Polychromatic418967fa.accept_11_3_10_7_1_129 47 54 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 54 150 2 23 27 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 54 150 3 15 18 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 54 150 2 22 27 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 54 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 54 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 150 6 7 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 150 (Polychromatic418967fa.accept_19_3_16_17_1_3826 41 54
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54 150 2 20 27 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 54 150 3 13 18 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 54 150 2 19 27 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 150
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 54 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 54 150 6 6 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 54 150 (Polychromatic418967fa.accept_13_9_2_7_1_1083 35 54 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 150 2 17 27 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 54 150 3 11 18 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 54 150 2 16 27 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 150 (Polychromatic418967fa.accept_13_5_2_7_1_2414
  31 54 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 150 6 5 9 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 150
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 54 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 54 150 2 14 27 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 54 150 3 9 18 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 54 150 2 13 27 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 54 150 (Polychromatic418967fa.accept_11_3_10_7_1_129 25 54 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 150 6 4 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 54 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 150 2 11 27 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 54 150 3 7 18 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 54 150 2 10 27 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 150
  (Polychromatic418967fa.accept_14_5_12_10_1_2985 19 54 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 150 6 3 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 150 (Polychromatic418967fa.accept_21_17_12_3_1_4848 17 54 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 150 2 8 27 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 54 150 3 5 18 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 54 150 2 7 27 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 150 (Polychromatic418967fa.accept_19_13_16_17_1_5140 13 54
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 150 6 2 9 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 150
  (Polychromatic418967fa.accept_17_11_3_14_1_6736 11 54 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 54 150 2 5 27 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 54 150 3 3 18 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 54 150 2 4 27 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 54 150 (Polychromatic418967fa.accept_19_7_16_17_1_6567 7 54 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 150 6 1 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 150 (Polychromatic418967fa.accept_13_5_2_7_1_2414 5 54 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 150 2 2 27 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 54 150 3 1 18 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 54 150 2 1 27 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 150
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 54 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 54 150)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 150 (allA_succ_of_accept 52 53
  150 (accept_3_4 52 53 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 53 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 50 53 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 150 (accept_3_4 49 53 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 150 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 53 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  53 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 150 (accept_3_4 46 53
  150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 150
  (Polychromatic418967fa.accept_13_6_1_7_1_1690 45 53 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 150 (Polychromatic418967fa.accept_27_17_26_15_1_5973 44 53 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 150 (accept_3_4 43 53 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 150 (Polychromatic418967fa.accept_13_3_1_7_1_1706 42 53 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 150 (Polychromatic418967fa.accept_7_6_4_3_1_266 41
  53 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 150 (accept_3_4 40 53
  150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 150 (Polychromatic418967fa.accept_4_3_1_2_1_62
  39 53 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 53 150
  (Polychromatic418967fa.accept_9_2_8_6_1_79 38 53 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 53 150 (accept_3_4 37 53 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  53 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 53 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 53 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 53 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 150 (accept_3_4 34 53 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 150 (Polychromatic418967fa.accept_16_1_5_6_1_4435 33 53 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 150
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 53 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 53 150 (accept_3_4 31 53 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  53 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 53 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 53 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 53 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 150 (accept_3_4 28 53 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 53 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 150
  (Polychromatic418967fa.accept_19_7_15_17_1_5198 26 53 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 53 150 (accept_3_4 25 53 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  53 150 (Polychromatic418967fa.accept_11_2_9_7_1_124 24 53 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 53 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 53 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 150 (accept_3_4 22 53 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 53 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 150
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 53 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 53 150 (accept_3_4 19 53 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  53 150 (Polychromatic418967fa.accept_21_18_11_3_1_8042 18 53 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 53 150 (Polychromatic418967fa.accept_16_1_5_6_1_4435 17 53 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 150 (accept_3_4 16 53 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 53 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 150
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 53 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 150 (accept_3_4 13 53 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  53 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 53 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 53 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 53 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 150 (accept_3_4 10 53 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 150 (Polychromatic418967fa.accept_20_9_13_10_1_452 9 53 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 150
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 53 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 150 (accept_3_4 7 53 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53
  150 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 53 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 53 150 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 53 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 150 (accept_3_4 4 53 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 53 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 53 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 150 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 53
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 150 (accept_3_4 1 53 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53 150)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 52 150 (allA_succ_of_accept 51 52 150 (Polychromatic418967fa.accept_12_3_4_6_1_434 51 52 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 52 150 2 25 26 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 52 150
  (Polychromatic418967fa.accept_9_4_7_6_1_255 49 52 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 52 150 2 24 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 52 150 (accept_3_5 47 52 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52
  150 2 23 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  52 150 (Polychromatic418967fa.accept_12_9_4_6_1_460 45 52 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 52 150 2 22 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 52 150 (Polychromatic418967fa.accept_16_11_4_6_1_4422 43 52 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 52 150 2 21 26 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 52 150 (accept_3_5 41 52 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52 150 2 20 26 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 52 150
  (Polychromatic418967fa.accept_9_3_7_6_1_76 39 52 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 52 150 2 19 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 52 150 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 52 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 52 150 2 18 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 52 150 (accept_3_5 35 52 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52 150 2 17 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 52 150 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 52 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 52 150 2 16 26 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 52 150
  (Polychromatic418967fa.accept_9_4_7_6_1_255 31 52 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 52 150 2 15 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 52 150 (accept_3_5 29 52 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52
  150 2 14 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  52 150 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 52 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 52 150 2 13 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 52 150 (Polychromatic418967fa.accept_20_5_12_10_1_5072 25 52 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 52 150 2 12 26 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 52 150 (accept_3_5 23 52 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52 150 2 11 26 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 52 150
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 52 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 52 150 2 10 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 52 150 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 52 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 52 150 2 9 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 52 150 (accept_3_5 17 52 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 52 150 2 8 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 52 150 (Polychromatic418967fa.accept_11_4_8_7_1_819 15 52 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 52 150 2 7 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 52 150 (Polychromatic418967fa.accept_9_4_7_6_1_255 13
  52 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 52 150 2 6 26 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 52 150 (accept_3_5 11
  52 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52 150 2 5 26 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 52 150
  (Polychromatic418967fa.accept_12_9_4_6_1_460 9 52 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 52 150 2 4 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 52 150 (Polychromatic418967fa.accept_21_7_10_3_1_1049 7 52 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 150 2 3 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 150 (accept_3_5 5 52 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 52 150 2 2 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 52 150 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 52 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 52 150 2 1 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 52 150 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 52
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  150)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 150 (allA_succ_of_accept 50 51 150
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 51 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 51 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 51 150 3 16 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 51 150 (Polychromatic418967fa.accept_7_5_2_3_1_106 47
  51 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 150
  (Polychromatic418967fa.accept_12_10_3_6_1_882 46 51 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 51 150 3 15 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 51 150 (Polychromatic418967fa.accept_12_8_3_6_1_909 44 51 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 51 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 150 3 14 17 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 51 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 51 150 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 51 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 51 150 3 13 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 51 150 (Polychromatic418967fa.accept_12_2_3_6_1_112 38
  51 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 37 51 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 51 150 3 12 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 51 150 (Polychromatic418967fa.accept_18_17_15_6_1_1797 35 51 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 51 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 150 3 11 17 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 150
  (Polychromatic418967fa.accept_12_8_3_6_1_909 32 51 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 150 (Polychromatic418967fa.accept_13_5_12_7_1_1080 31 51 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 51 150 3 10 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 51 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 51
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 150
  (Polychromatic418967fa.accept_12_4_3_6_1_879 28 51 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 51 150 3 9 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 51 150 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 51 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 51 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 150 3 8 17 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 150
  (Polychromatic418967fa.accept_13_10_12_7_1_1079 23 51 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 51 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 150 3 7 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 51 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 150
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 51 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 51 150 3 6 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 51 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 51 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 150 (Polychromatic418967fa.accept_12_4_3_6_1_879 16 51 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 150 3 5 17 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 150
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 51 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 51 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 150 3 4 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 150 (Polychromatic418967fa.accept_13_11_12_7_1_2443 11 51
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 150
  (Polychromatic418967fa.accept_12_10_3_6_1_882 10 51 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 51 150 3 3 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 51 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 51 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 150 (Polychromatic418967fa.accept_19_7_13_17_1_8041 7 51 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 150 3 2 17 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 51 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 150 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 51 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 150 3 1 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 150 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 51 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 51 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 51 150))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 150 (allA_succ_of_accept 49 50 150
  (accept_3_4 49 50 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 50 150 2 24 25 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 50 150
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 50 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 50 150 2 23 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 50 150 5 9 10 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 50 150 2 22 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 50 150 (accept_3_4 43 50 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50
  150 2 21 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  50 150 (Polychromatic418967fa.accept_16_9_2_6_1_4434 41 50 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 50 150 10 4 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 50 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 50 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 50 150 2 19 25 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 50 150 (accept_3_4 37 50 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50 150 2 18 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 50 150 5 7 10 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 50 150 2 17 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 33
  50 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 50 150 2 16 25 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 50 150 (accept_3_4 31
  50 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50 150 10 3 5 15 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 50 150
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 50 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 50 150 2 14 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 50 150 (Polychromatic418967fa.accept_12_3_2_6_1_138 27 50 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 150 2 13 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 50 150 25 1 2 6 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 50 150 2 12 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 150 (Polychromatic418967fa.accept_7_2_1_3_1_102 23
  50 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 50 150 2 11 25 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 50 150
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 50 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 50 150 10 2 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 50 150 (accept_3_4 19 50 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50
  150 2 9 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  50 150 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 50 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 50 150 2 8 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 50 150 5 3 10 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 50 150 2 7 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 50 150 (accept_3_4 13 50 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 50 150 2 6 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 50 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 50 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 50 150 10 1 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 50 150 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 50 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 150 2 4 25 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 150 (accept_3_4 7 50 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 150 2 3 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 50 150 5 1 10 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 50 150 2 2 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 50
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 150 2 1 25 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 150 (accept_3_4 1 50
  150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 150))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 49 150 (allA_succ_of_accept 48 49 150 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 49 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 150 (accept_3_5 47 49 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 49 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 150
  (Polychromatic418967fa.accept_14_3_7_10_1_2146 45 49 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 150 (accept_3_5 44 49 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 49 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 49 150 (Polychromatic418967fa.accept_11_9_5_7_1_815 42 49 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 150 (accept_3_5 41 49 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 150 (Polychromatic418967fa.accept_17_6_15_14_1_8027 40 49 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 49 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 150 (accept_3_5 38 49 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 49 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 150 (Polychromatic418967fa.accept_20_16_9_10_1_6513 36 49 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 150 (accept_3_5 35 49 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 150 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 49 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 150
  (Polychromatic418967fa.accept_17_16_15_14_1_6747 33 49 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 49 150 (accept_3_5 32 49 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 49 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 49 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 150 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 49 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 150 (accept_3_5 29 49 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 28
  49 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 49 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 150 (accept_3_5 26 49 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 150 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 49 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 150 (Polychromatic418967fa.accept_19_5_11_17_1_6536 24 49 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 150 (accept_3_5 23 49 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 150 (Polychromatic418967fa.accept_21_1_7_3_1_6450 22 49 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 150
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 49 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 150 (accept_3_5 20 49 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 49 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 150 (Polychromatic418967fa.accept_14_4_7_10_1_3888 18 49 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 150 (accept_3_5 17 49 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 150 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 49 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 49 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 150 (accept_3_5 14 49 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 150 (Polychromatic418967fa.accept_19_13_11_17_1_5152 13 49 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 150 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 49 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 150 (accept_3_5 11 49 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 49 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 150
  (Polychromatic418967fa.accept_11_9_5_7_1_815 9 49 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 150 (accept_3_5 8 49 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  150 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 49 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 49 150 (Polychromatic418967fa.accept_17_6_15_14_1_8027 6 49 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 150 (accept_3_5 5 49 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 150 (Polychromatic418967fa.accept_13_4_10_7_1_1701 4 49 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 49
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 150 (accept_3_5 2 49 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 49
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49
  150))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 150 (allA_succ_of_accept 47 48 150
  (Polychromatic418967fa.accept_9_2_3_6_1_88 47 48 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 48 150 2 23 24 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 48 150 3 15 16 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 48 150 2 22 24 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 48 150 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 48 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 150 6 7 8 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 150 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 48 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 150 2 20 24 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 48 150 3 13 16 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 48 150 2 19 24 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 150
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 48 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 150 6 6 8 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 48 150 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 48 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 150 2 17 24 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 48 150 3 11 16 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 48 150 2 16 24 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 150 (Polychromatic418967fa.accept_9_4_3_6_1_532 31
  48 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 150 6 5 8 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 150
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 48 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 48 150 2 14 24 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 48 150 3 9 16 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 48 150 2 13 24 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 48 150 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 48 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 150 6 4 8 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 48 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 150 2 11 24 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 48 150 3 7 16 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 48 150 2 10 24 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 150
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 48 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 48 150 6 3 8 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 48 150 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 48 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 150 2 8 24 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 48 150 3 5 16 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 48 150 2 7 24 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 150 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 48 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 150 6 2 8 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 150
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 48 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 48 150 2 5 24 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 48 150 3 3 16 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 48 150 2 4 24 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 150 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 48 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 150 6 1 8 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 150 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 48 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 150 2 2 24 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 48 150 3 1 16 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 48 150 2 1 24 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 150
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 48 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 48 150)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 150 (allA_succ_of_accept 46 47 150
  (accept_3_4 46 47 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 47 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 47 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 150 (accept_3_4 43 47 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 150 (Polychromatic418967fa.accept_13_3_8_7_1_4135 42 47 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 41
  47 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 150 (accept_3_4 40 47
  150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 150
  (Polychromatic418967fa.accept_9_3_2_6_1_264 39 47 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 150 (Polychromatic418967fa.accept_13_12_8_7_1_2526 38 47 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 150 (accept_3_4 37 47 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 47 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 150 (Polychromatic418967fa.accept_9_8_2_6_1_875 35
  47 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 150 (accept_3_4 34 47
  150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 150 (Polychromatic418967fa.accept_4_1_3_2_1_3
  33 47 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 150
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 47 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 150 (accept_3_4 31 47 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  47 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 47 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 47 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 47 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 150 (accept_3_4 28 47 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 150 (Polychromatic418967fa.accept_13_1_8_7_1_1088 27 47 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 150
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 47 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 47 150 (accept_3_4 25 47 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  47 150 (Polychromatic418967fa.accept_27_24_20_15_1_8040 24 47 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 47 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 47 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 150 (accept_3_4 22 47 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 47 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 150
  (Polychromatic418967fa.accept_19_1_9_17_1_8039 20 47 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 47 150 (accept_3_4 19 47 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  47 150 (Polychromatic418967fa.accept_17_1_13_14_1_478 18 47 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 47 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 47 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 150 (accept_3_4 16 47 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 47 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 150
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 47 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 150 (accept_3_4 13 47 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  47 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 47 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 47 150 (Polychromatic418967fa.accept_19_11_9_17_1_8038 11 47 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 150 (accept_3_4 10 47 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 47 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 150
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 47 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 150 (accept_3_4 7 47 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47
  150 (Polychromatic418967fa.accept_19_6_9_17_1_5214 6 47 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 47 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 47 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 150 (accept_3_4 4 47 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 47 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 150
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 47 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 47 150 (accept_3_4 1 47 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47
  150))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 150 (allA_succ_of_accept 45 46 150
  (Polychromatic418967fa.accept_12_9_10_6_1_872 45 46 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 46 150 2 22 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 46 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 46 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 150 2 21 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 150 (accept_3_5 41 46 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 150 2 20 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 150 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 46 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 46 150 2 19 23 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 46 150
  (Polychromatic418967fa.accept_24_13_22_6_1_8037 37 46 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 46 150 2 18 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 46 150 (accept_3_5 35 46 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46
  150 2 17 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  46 150 (Polychromatic418967fa.accept_12_9_10_6_1_872 33 46 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 46 150 2 16 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 46 150 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 46 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 46 150 2 15 23 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 46 150 (accept_3_5 29 46 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 46 150 2 14 23 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 46 150
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 46 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 46 150 2 13 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 46 150 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 46 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 150 2 12 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 150 (accept_3_5 23 46 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 150 2 11 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 46 150 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 46 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 46 150 2 10 23 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 46 150
  (Polychromatic418967fa.accept_20_19_6_10_1_3651 19 46 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 46 150 2 9 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 46 150 (accept_3_5 17 46 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46
  150 2 8 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  46 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 46 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 46 150 2 7 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 46 150 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 46 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 150 2 6 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 150 (accept_3_5 11 46 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 150 2 5 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 46 150 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 46 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 46 150 2 4 23 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 46 150
  (Polychromatic418967fa.accept_9_7_1_6_1_261 7 46 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 46 150 2 3 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 46 150 (accept_3_5 5 46 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 46 150
  2 2 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 46
  150 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 46 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 46 150 2 1 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 46 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 46 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 46 150)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 150
  (allA_succ_of_accept 44 45 150 (Polychromatic418967fa.accept_12_8_9_6_1_127 44 45 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 45 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 150 3 14 15 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 150
  (Polychromatic418967fa.accept_14_13_3_10_1_2159 41 45 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 45 150 5 8 9 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 45 150 3 13 15 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 45 150 (Polychromatic418967fa.accept_12_2_9_6_1_439 38 45 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 150 (Polychromatic418967fa.accept_17_3_11_14_1_2071 37 45
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 150 3 12 15 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 45 150 5 7 9 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 45 150
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 34 45 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 45 150 3 11 15 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 45 150 (Polychromatic418967fa.accept_12_8_9_6_1_127 32 45 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 45 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 150 15 2 3 10 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 150
  (Polychromatic418967fa.accept_17_12_11_14_1_3120 29 45 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 45 150 (Polychromatic418967fa.accept_11_6_1_7_1_1315 28 45 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 45 150 3 9 15 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 45 150 (Polychromatic418967fa.accept_12_2_9_6_1_439 26
  45 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 45 150 5 5 9 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 45 150 3 8 15 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 45 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 45 150 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 45 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 45 150 3 7 15 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 45 150 5 4 9 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 45 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 45 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 150 3 6 15 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 150
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 45 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 150 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 45 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 150 15 1 3 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 150 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 45 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 150
  (Polychromatic418967fa.accept_14_13_3_10_1_2159 13 45 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 45 150 3 4 15 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 45 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 45 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 45 150 5 2 9 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 45 150 3 3 15 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 150 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 45 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 45 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 45 150 3 2 15 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 45 150 5 1 9 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 45 150 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 45 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 45 150 3 1 15 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 45 150 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 45 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 150
  (Polychromatic418967fa.accept_13_1_6_7_1_550 1 45 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 45 150))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 150 (allA_succ_of_accept 43 44 150
  (accept_3_4 43 44 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 44 150 2 21 22 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 44 150
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 44 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 44 150 2 20 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 44 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 44 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 150 2 19 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 150 (accept_3_4 37 44 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 150 2 18 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 150 (Polychromatic418967fa.accept_17_1_10_14_1_1173 35 44
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 150 2 17 22 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 44 150
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 44 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 44 150 2 16 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 44 150 (accept_3_4 31 44 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44
  150 2 15 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  44 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 44 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 44 150 2 14 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 44 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 44 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 44 150 2 13 22 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 44 150 (accept_3_4 25 44 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44 150 2 12 22 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 44 150
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 44 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 44 150 2 11 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 44 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 44 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 150 2 10 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 150 (accept_3_4 19 44 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44 150 2 9 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 44 150 (Polychromatic418967fa.accept_21_17_2_3_1_4942 17 44 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 44 150 2 8 22 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 44 150
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 44 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 44 150 2 7 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 44 150 (accept_3_4 13 44 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44
  150 2 6 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  44 150 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 44 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 44 150 2 5 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 44 150 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 44 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 150 2 4 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 150 (accept_3_4 7 44 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 150 2 3 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 44 150 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 44 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 44 150 2 2 22 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 44 150
  (Polychromatic418967fa.accept_9_3_8_6_1_80 3 44 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 44 150 2 1 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 44 150 (accept_3_4 1 44 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44
  150)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 150 (allA_succ_of_accept 42 43 150
  (Polychromatic418967fa.accept_13_3_4_7_1_1711 42 43 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 150 (accept_3_5 41 43 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 43 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 43 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 150 (accept_3_5 38 43 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 43 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 150
  (Polychromatic418967fa.accept_11_3_10_7_1_129 36 43 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 150 (accept_3_5 35 43 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 150 (Polychromatic418967fa.accept_16_2_11_6_1_737 34 43 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 43 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 150 (accept_3_5 32 43 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 150 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 43 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 150
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 43 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 150 (accept_3_5 29 43 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 150 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 43 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 150 (Polychromatic418967fa.accept_18_9_7_6_1_5331 27 43 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 150 (accept_3_5 26 43 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 43 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 150
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 24 43 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 150 (accept_3_5 23 43 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 150 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 43 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 43 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 150 (accept_3_5 20 43 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 43 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 150
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 43 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 150 (accept_3_5 17 43 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 150 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 43 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 150 (Polychromatic418967fa.accept_19_15_5_17_1_8036 15 43 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 150 (accept_3_5 14 43 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 43 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 150
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 43 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 150 (accept_3_5 11 43 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 150 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 43 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 43 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 150 (accept_3_5 8 43 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 150 (Polychromatic418967fa.accept_19_7_5_17_1_3849 7 43 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 150
  (Polychromatic418967fa.accept_13_6_4_7_1_2464 6 43 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 150 (accept_3_5 5 43 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  150 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 43 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 150 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 43 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 150 (accept_3_5 2 43 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 43 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 150))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 150
  (allA_succ_of_accept 41 42 150 (Polychromatic418967fa.accept_17_7_8_14_1_6720 41 42 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 150 2 20 21 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 42 150 3 13 14 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 42 150 2 19 21 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 150 (Polychromatic418967fa.accept_13_11_3_7_1_2513
  37 42 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 150 6 6 7 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 150
  (Polychromatic418967fa.accept_11_2_9_7_1_124 35 42 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 42 150 2 17 21 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 42 150 3 11 14 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 42 150 2 16 21 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 42 150 (Polychromatic418967fa.accept_22_9_20_18_1_8035 31 42 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 150 6 5 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 150 (Polychromatic418967fa.accept_19_10_4_17_1_1544 29 42
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 150 2 14 21 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 42 150 3 9 14 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 42 150 2 13 21 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 150
  (Polychromatic418967fa.accept_19_6_4_17_1_6540 25 42 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 150 6 4 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 150 (Polychromatic418967fa.accept_13_10_3_7_1_2517 23 42 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 150 2 11 21 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 42 150 3 7 14 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 42 150 2 10 21 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 150 (Polychromatic418967fa.accept_24_19_18_6_1_8034
  19 42 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 150 6 3 7 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 150
  (Polychromatic418967fa.accept_13_4_3_7_1_2515 17 42 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 42 150 2 8 21 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 42 150 3 5 14 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 42 150 2 7 21 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 42 150 (Polychromatic418967fa.accept_11_2_9_7_1_124 13 42 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 150 6 2 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 150 (Polychromatic418967fa.accept_13_11_3_7_1_2513 11 42 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 150 2 5 21 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 42 150 3 3 14 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 42 150 2 4 21 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 150
  (Polychromatic418967fa.accept_17_7_8_14_1_6720 7 42 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 42 150 6 1 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 42 150 (Polychromatic418967fa.accept_11_5_9_7_1_411 5 42 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 150 2 2 21 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 42 150 3 1 14 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 42 150 2 1 21 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 150 (Polychromatic418967fa.accept_13_1_3_7_1_1710 1 42 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  150)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 150 (allA_succ_of_accept 40 41 150 (accept_3_4 40 41 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 39
  41 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 41 150
  (Polychromatic418967fa.accept_9_2_5_6_1_536 38 41 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 41 150 (accept_3_4 37 41 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  41 150 (Polychromatic418967fa.accept_23_13_18_12_1_8033 36 41 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 41 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 41 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 150 (accept_3_4 34 41 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 150 (Polychromatic418967fa.accept_18_15_5_6_1_5293 33 41 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 150
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 41 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 150 (accept_3_4 31 41 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  41 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 41 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 150 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 41 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 150 (accept_3_4 28 41 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 41 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 150
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 41 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 150 (accept_3_4 25 41 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 150 (Polychromatic418967fa.accept_19_5_3_17_1_6557 24 41 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 41 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 150 (accept_3_4 22 41 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 41 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 150
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 41 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 150 (accept_3_4 19 41 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 150 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 41 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 150 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 41 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 150 (accept_3_4 16 41 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 41 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 150
  (Polychromatic418967fa.accept_19_14_3_17_1_6558 14 41 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 150 (accept_3_4 13 41 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 41 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 41 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 150 (accept_3_4 10 41 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 41 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 150
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 41 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 150 (accept_3_4 7 41 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  150 (Polychromatic418967fa.accept_17_6_7_14_1_6704 6 41 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 41 150 (Polychromatic418967fa.accept_13_5_2_7_1_2414 5 41 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 150 (accept_3_4 4 41 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 41 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 41 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 150
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 41 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 41 150 (accept_3_4 1 41 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41
  150))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 150 (allA_succ_of_accept 39 40 150
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 40 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 40 150 2 19 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 40 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 40 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 150 2 18 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 40 150 5 7 8 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 40 150 2 17 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 40 150 (Polychromatic418967fa.accept_12_9_4_6_1_460 33
  40 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 40 150 2 16 20 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 40 150
  (Polychromatic418967fa.accept_19_12_2_17_1_5210 31 40 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 40 150 10 3 4 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 40 150 (accept_3_5 29 40 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40
  150 2 14 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  40 150 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 40 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 40 150 2 13 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 25 40 150 5 5 8 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 40 150 2 12 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 40 150 (accept_3_5 23 40 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 40 150 2 11 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 40 150 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 40 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 40 150 10 2 4 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 40 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 40 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 150 2 9 20 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 150 (accept_3_5 17 40 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 40 150 2 8 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 40 150 5 3 8 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 40 150 2 7 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 40 150 (Polychromatic418967fa.accept_24_13_16_6_1_8032
  13 40 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 150 2 6 20 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 150 (accept_3_5 11
  40 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 150 10 1 4 15 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 150
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 40 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 40 150 2 4 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 40 150 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 40 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 150 2 3 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 40 150 5 1 8 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 40 150 2 2 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 40 150 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 40 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 150 2 1 20 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 150
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 40 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 150)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 150 (allA_succ_of_accept 38 39 150
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 39 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 39 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 150 3 12 13 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 150 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  39 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 150
  (Polychromatic418967fa.accept_7_6_4_3_1_266 34 39 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 150 3 11 13 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 150 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 39 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 150 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 39 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 150 3 10 13 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 39 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 150 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 39 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 150 3 9 13 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 150 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 39 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 39 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 150 3 8 13 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 150 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 39 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 39 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 150 3 7 13 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 150
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 39 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 150 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 39 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 150 3 6 13 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 39 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 150
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 39 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 150 3 5 13 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 150 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 39 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 39 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 150 3 4 13 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 150
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 39 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 150 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 39 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 150 3 3 13 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 39 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 150
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 39 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 150 3 2 13 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 39 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 150 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 39 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 150 3 1 13 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 150
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 39 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 39 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 150))))))))))))))))))))))))))))))))))))))) (allB_succ 38 150
  (allA_succ_of_accept 37 38 150 (accept_3_4 37 38 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  150 2 18 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  38 150 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 38 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 150 2 17 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 150 (Polychromatic418967fa.accept_12_9_2_6_1_455 33 38 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 150 2 16 19 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 150 (accept_3_4 31 38 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 150 2 15 19 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 150
  (Polychromatic418967fa.accept_21_8_17_3_1_8031 29 38 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 150 2 14 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 38 150 (Polychromatic418967fa.accept_12_3_2_6_1_138 27 38 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 150 2 13 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 150 (accept_3_4 25 38 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 150 2 12 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 150 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 38 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 150 2 11 19 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 150
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 38 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 150 2 10 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 38 150 (accept_3_4 19 38 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38
  150 2 9 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  38 150 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 38 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 38 150 2 8 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 38 150 (Polychromatic418967fa.accept_12_3_2_6_1_138 15 38 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 150 2 7 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 150 (accept_3_4 13 38 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 150 2 6 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 38 150 (Polychromatic418967fa.accept_13_11_12_7_1_2443 11 38 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 38 150 2 5 19 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 38 150
  (Polychromatic418967fa.accept_11_9_5_7_1_815 9 38 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 38 150 2 4 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 38 150 (accept_3_4 7 38 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 150
  2 3 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38
  150 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 38 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 38 150 2 2 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 38 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 38 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 150 2 1 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 150 (accept_3_4 1 38 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 38 150)))))))))))))))))))))))))))))))))))))) (allB_succ 37 150 (allA_succ_of_accept 36 37 150
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 37 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 150 (accept_3_5 35 37 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 37 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 150 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 37 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 150 (accept_3_5 32 37 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 37 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 150
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 37 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 150 (accept_3_5 29 37 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 150 (Polychromatic418967fa.accept_17_11_3_14_1_6736 28 37 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 37 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 150 (accept_3_5 26 37 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 150 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 37 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 150
  (Polychromatic418967fa.accept_19_5_18_17_1_8017 24 37 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 150 (accept_3_5 23 37 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 37 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 150 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 37 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 150 (accept_3_5 20 37 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 37 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 150
  (Polychromatic418967fa.accept_13_5_11_7_1_559 18 37 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 150 (accept_3_5 17 37 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 150 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 37 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 37 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 150 (accept_3_5 14 37 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 37 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 150
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 37 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 150 (accept_3_5 11 37 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 150 (Polychromatic418967fa.accept_19_10_18_17_1_8030 10 37 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 150 (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 37 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 150 (accept_3_5 8 37 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 37 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 150
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 37 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 150 (accept_3_5 5 37 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  150 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 37 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 37 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 150 (accept_3_5 2 37 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 37 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 150))))))))))))))))))))))))))))))))))))) (allB_succ 36 150
  (allA_succ_of_accept 35 36 150 (Polychromatic418967fa.accept_16_3_4_6_1_6798 35 36 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 150 2 17 18 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 36 150 3 11 12 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 36 150 2 16 18 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 150 (Polychromatic418967fa.accept_21_10_15_3_1_6431
  31 36 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 150 6 5 6 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 150
  (Polychromatic418967fa.accept_13_3_10_7_1_1061 29 36 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 36 150 2 14 18 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 36 150 3 9 12 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 36 150 2 13 18 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 36 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 150 6 4 6 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 150 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 36 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 150 2 11 18 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 36 150 3 7 12 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 36 150 2 10 18 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 150
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 36 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 150 6 3 6 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 150 (Polychromatic418967fa.accept_13_4_10_7_1_1701 17 36 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 150 2 8 18 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 36 150 3 5 12 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 36 150 2 7 18 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 150 (Polychromatic418967fa.accept_16_13_4_6_1_2322 13 36 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 150 6 2 6 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 150
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 36 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 36 150 2 5 18 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 36 150 3 3 12 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 36 150 2 4 18 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 36 150 (Polychromatic418967fa.accept_21_7_15_3_1_8029 7 36 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 150 6 1 6 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 36 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 150 2 2 18 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 36 150 3 1 12 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 36 150 2 1 18 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 150
  (Polychromatic418967fa.accept_21_1_15_3_1_4817 1 36 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 150)))))))))))))))))))))))))))))))))))) (allB_succ 35 150 (allA_succ_of_accept 34 35 150 (accept_3_4 34
  35 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 35 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 150 (Polychromatic418967fa.accept_9_5_8_6_1_281 32 35 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 150 (accept_3_4 31 35 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 35 150 5 6 7 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 35 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 35 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 150 (accept_3_4 28 35 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 150 (Polychromatic418967fa.accept_16_11_3_6_1_4462 27 35 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 150
  (Polychromatic418967fa.accept_19_7_16_17_1_6567 26 35 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 35 150 5 5 7 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 35 150 (Polychromatic418967fa.accept_13_11_9_7_1_2484 24 35 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 150 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 35 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 150 (accept_3_4 22 35 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 21
  35 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 35 150 5 4 7 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 35 150 (accept_3_4 19
  35 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 150
  (Polychromatic418967fa.accept_14_4_7_10_1_3888 18 35 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 35 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 35 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 150 (accept_3_4 16 35 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 35 150 5 3 7 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 35 150 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 35 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 150 (accept_3_4 13 35 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 35 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 150
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 35 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 35 150 5 2 7 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 35 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 35 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 150 (Polychromatic418967fa.accept_13_8_9_7_1_530 8 35 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 150 (accept_3_4 7 35 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 150 (Polychromatic418967fa.accept_13_6_9_7_1_2430 6
  35 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 35 150 5 1 7 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 35 150 (accept_3_4 4 35
  150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 150 (Polychromatic418967fa.accept_9_3_8_6_1_80
  3 35 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 150
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 35 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 150 (accept_3_4 1 35 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  150))))))))))))))))))))))))))))))))))) (allB_succ 34 150 (allA_succ_of_accept 33 34 150
  (Polychromatic418967fa.accept_12_9_10_6_1_872 33 34 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 34 150 2 16 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 34 150 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 34 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 150 2 15 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 150 (accept_3_5 29 34 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34 150 2 14 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 34 150 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 34 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 150 2 13 17 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 150
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 34 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 34 150 2 12 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 34 150 (accept_3_5 23 34 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34
  150 2 11 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  34 150 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 34 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 34 150 2 10 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 34 150 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 34 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 150 2 9 17 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 150 (accept_3_5 17 34 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 34 150 2 8 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 34 150 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 34 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 150 2 7 17 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 150
  (Polychromatic418967fa.accept_9_4_7_6_1_255 13 34 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 34 150 2 6 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 34 150 (accept_3_5 11 34 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34
  150 2 5 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  34 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 34 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 34 150 2 4 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 34 150 (Polychromatic418967fa.accept_19_7_15_17_1_5198 7 34 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 150 2 3 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 150 (accept_3_5 5 34 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 34 150 2 2 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 34 150 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 34 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 150 2 1 17 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 150
  (Polychromatic418967fa.accept_9_1_7_6_1_75 1 34 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 150)))))))))))))))))))))))))))))))))) (allB_succ 33 150 (allA_succ_of_accept 32 33 150
  (Polychromatic418967fa.accept_12_8_9_6_1_127 32 33 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 33 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 33 150 3 10 11 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 33 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 29
  33 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 150
  (Polychromatic418967fa.accept_12_4_9_6_1_440 28 33 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 33 150 3 9 11 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 33 150 (Polychromatic418967fa.accept_12_2_9_6_1_439 26 33 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 150 (Polychromatic418967fa.accept_17_8_16_14_1_4261 25 33
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 150 3 8 11 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 33 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 33 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 33 150 3 7 11 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 33 150 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 33 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 33 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 33 150 3 6 11 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 33 150 (Polychromatic418967fa.accept_18_17_15_6_1_1797 17 33 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 33 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 150 3 5 11 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 150
  (Polychromatic418967fa.accept_12_2_9_6_1_439 14 33 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 150 (Polychromatic418967fa.accept_21_13_12_3_1_8028 13 33 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 33 150 3 4 11 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 33 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 33 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 150
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 33 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 33 150 3 3 11 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 33 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 33 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 33 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 150 3 2 11 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 150
  (Polychromatic418967fa.accept_16_5_1_6_1_3367 5 33 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 150 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 33 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 33 150 3 1 11 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 33 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 33 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 150
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 33 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 33 150))))))))))))))))))))))))))))))))) (allB_succ 32 150 (allA_succ_of_accept 31 32 150 (accept_3_4 31 32
  150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32 150 2 15 16 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 32 150
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 32 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 32 150 2 14 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 32 150 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 32 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 150 2 13 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 150 (accept_3_4 25 32 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 150 2 12 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 150 (Polychromatic418967fa.accept_17_6_15_14_1_8027 23 32
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 150 2 11 16 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 150
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 32 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 150 2 10 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 150 (accept_3_4 19 32 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32
  150 2 9 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  32 150 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 32 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 32 150 2 8 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 32 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 32 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 150 2 7 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 150 (accept_3_4 13 32 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 150 2 6 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 32 150 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 32 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 150 2 5 16 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 150
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 32 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 32 150 2 4 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 32 150 (accept_3_4 7 32 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 150
  2 3 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32
  150 (Polychromatic418967fa.accept_20_5_12_10_1_5072 5 32 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 32 150 2 2 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 32 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 32 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 150 2 1 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 150 (accept_3_4 1 32 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 32 150)))))))))))))))))))))))))))))))) (allB_succ 31 150 (allA_succ_of_accept 30 31 150
  (Polychromatic418967fa.accept_9_3_4_6_1_252 30 31 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 150 (accept_3_5 29 31 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 31 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 150 (Polychromatic418967fa.accept_11_5_9_7_1_411 27 31 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 150 (accept_3_5 26 31 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 31 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 150
  (Polychromatic418967fa.accept_11_2_9_7_1_124 24 31 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 150 (accept_3_5 23 31 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 150 (Polychromatic418967fa.accept_19_3_12_17_1_6585 22 31 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 31 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 150 (accept_3_5 20 31 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 31 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 150
  (Polychromatic418967fa.accept_19_18_12_17_1_8026 18 31 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 31 150 (accept_3_5 17 31 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 31 150 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 31 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 150 (Polychromatic418967fa.accept_13_2_5_7_1_1695 15 31 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 150 (accept_3_5 14 31 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 13
  31 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 150
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 31 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 150 (accept_3_5 11 31 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 31 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 31 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 150 (accept_3_5 8 31 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 150 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 31 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 150
  (Polychromatic418967fa.accept_14_6_3_10_1_3905 6 31 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 150 (accept_3_5 5 31 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  150 (Polychromatic418967fa.accept_20_4_11_10_1_8025 4 31 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 31 150 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 31 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 150 (accept_3_5 2 31 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 31 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 150))))))))))))))))))))))))))))))) (allB_succ 30 150
  (allA_succ_of_accept 29 30 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 30 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30 150 2 14 15 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 30 150 3 9 10 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 30 150 2 13 15 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 30 150 5 5 6 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 30 150 6 4 5 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 150 (Polychromatic418967fa.accept_9_5_3_6_1_269 23
  30 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 150 2 11 15 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 30 150 3 7 10 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 30 150 10 2 3 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 150
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 30 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 30 150 6 3 5 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 30 150 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 30 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 150 2 8 15 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 30 150 15 1 2 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 30 150 2 7 15 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 30 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 150 6 2 5 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 150
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 30 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 30 150 10 1 3 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 30 150 3 3 10 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 30 150 2 4 15 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 150 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 30 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 150 6 1 5 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 30 150 5 1 6 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 30 150 2 2 15 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 30 150 3 1 10 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 30 150 2 1 15 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 30 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 150)))))))))))))))))))))))))))))) (allB_succ
  29 150 (allA_succ_of_accept 28 29 150 (accept_3_4 28 29 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 29 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 29 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 29 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 150 (accept_3_4 25 29 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 150 (Polychromatic418967fa.accept_13_11_3_7_1_2513
  24 29 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 29 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 150 (accept_3_4 22 29 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 29 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 150 (Polychromatic418967fa.accept_16_4_13_6_1_4417 20 29 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 150 (accept_3_4 19 29 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 29 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 150
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 29 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 150 (accept_3_4 16 29 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 29 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 150 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 29 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 150 (accept_3_4 13 29 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 29 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 29 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 150 (accept_3_4 10 29 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 150 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 29 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 150 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 29 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 150 (accept_3_4 7 29 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 150 (Polychromatic418967fa.accept_20_6_9_10_1_8024 6 29 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 150
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 29 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 150 (accept_3_4 4 29 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  150 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 29 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 150 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 29 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 150 (accept_3_4 1 29 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 150))))))))))))))))))))))))))))) (allB_succ 28 150 (allA_succ_of_accept 27 28 150
  (Polychromatic418967fa.accept_12_3_4_6_1_434 27 28 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 28 150 2 13 14 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 28 150 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 28 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 150 2 12 14 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 150 (accept_3_5 23 28 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28 150 2 11 14 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 28 150 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 28 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 28 150 2 10 14 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 28 150
  (Polychromatic418967fa.accept_23_19_5_12_1_8023 19 28 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 28 150 2 9 14 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 28 150 (accept_3_5 17 28 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28
  150 2 8 14 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  28 150 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 28 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 28 150 2 7 14 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 28 150 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 28 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 150 2 6 14 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 150 (accept_3_5 11 28 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28 150 2 5 14 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 28 150 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 28 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 28 150 2 4 14 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 28 150
  (Polychromatic418967fa.accept_9_7_1_6_1_261 7 28 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 28 150 2 3 14 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 28 150 (accept_3_5 5 28 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 150
  2 2 14 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 28
  150 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 28 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 28 150 2 1 14 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 28 150 (Polychromatic418967fa.accept_11_1_6_7_1_116 1 28 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 28 150)))))))))))))))))))))))))))) (allB_succ 27 150 (allA_succ_of_accept 26
  27 150 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 27 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 27 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 27 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 150 3 8 9 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 23
  27 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 150
  (Polychromatic418967fa.accept_12_10_3_6_1_882 22 27 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 27 150 3 7 9 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 27 150 (Polychromatic418967fa.accept_11_9_5_7_1_815 20 27 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 150 (Polychromatic418967fa.accept_13_6_1_7_1_1690 19 27 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 150 3 6 9 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 27 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 27 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 150 3 5 9 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 150 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 27 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 27 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 27 150 3 4 9 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 27 150 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 27 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 150 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 27 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 150 3 3 9 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 150
  (Polychromatic418967fa.accept_12_8_3_6_1_909 8 27 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 150 (Polychromatic418967fa.accept_17_7_10_14_1_8022 7 27 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 150 3 2 9 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 27 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 150
  (Polychromatic418967fa.accept_7_4_6_3_1_271 4 27 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 27 150 3 1 9 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 27 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 27 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 27 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 150))))))))))))))))))))))))))) (allB_succ 26
  150 (allA_succ_of_accept 25 26 150 (accept_3_4 25 26 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24
  26 150 2 12 13 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  23 26 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 26 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 150 2 11 13 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 26 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 26 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 150 2 10 13 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 150 (accept_3_4 19 26 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 150 2 9 13 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 150 (Polychromatic418967fa.accept_22_17_4_18_1_8021
  17 26 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 150 2 8 13 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 150
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 26 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 150 2 7 13 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 26 150 (accept_3_4 13 26 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26
  150 2 6 13 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  26 150 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 26 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 26 150 2 5 13 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 26 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 26 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 150 2 4 13 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 150 (accept_3_4 7 26 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 150 2 3 13 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 26 150 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 26 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 150 2 2 13 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 150
  (Polychromatic418967fa.accept_9_3_8_6_1_80 3 26 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 26 150 2 1 13 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 26 150 (accept_3_4 1 26 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  150)))))))))))))))))))))))))) (allB_succ 25 150 (allA_succ_of_accept 24 25 150
  (Polychromatic418967fa.accept_13_11_12_7_1_2443 24 25 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 150 (accept_3_5 23 25 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 25 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 150 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 25 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 25 150 5 4 5 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 25 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 19
  25 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 150
  (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 25 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 150 (accept_3_5 17 25 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 150 (Polychromatic418967fa.accept_17_16_8_14_1_6757 16 25 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 25 150 5 3 5 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 25 150 (accept_3_5 14 25 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 25 150 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 25 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 150 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 25 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 150 (accept_3_5 11 25 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 25 150 5 2 5 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 25 150 (Polychromatic418967fa.accept_18_9_7_6_1_5331 9
  25 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 150 (accept_3_5 8 25 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 25
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 150
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 25 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 25 150 5 1 5 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 25 150 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 25 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 25 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 150 (accept_3_5 2 25 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 25
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 150))))))))))))))))))))))))) (allB_succ
  24 150 (allA_succ_of_accept 23 24 150 (Polychromatic418967fa.accept_17_6_7_14_1_6704 23 24 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 150 2 11 12 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 24 150 3 7 8 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 24 150 2 10 12 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 150
  (Polychromatic418967fa.accept_27_19_24_15_1_8020 19 24 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 24 150 6 3 4 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 24 150 (Polychromatic418967fa.accept_13_4_11_7_1_558 17 24 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 150 2 8 12 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 24 150 3 5 8 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 24 150 2 7 12 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 150 (Polychromatic418967fa.accept_22_13_2_18_1_4747
  13 24 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 150 6 2 4 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 150
  (Polychromatic418967fa.accept_19_11_5_17_1_2620 11 24 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 24 150 2 5 12 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 24 150 3 3 8 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 24 150 2 4 12 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 150 (Polychromatic418967fa.accept_19_7_5_17_1_3849 7 24 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 150 6 1 4 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 150 (Polychromatic418967fa.accept_13_5_11_7_1_559 5 24 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 150 2 2 12 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 24 150 3 1 8 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 24 150 2 1 12 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 150
  (Polychromatic418967fa.accept_13_1_11_7_1_1704 1 24 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 24 150)))))))))))))))))))))))) (allB_succ 23 150 (allA_succ_of_accept 22 23 150 (accept_3_4 22 23 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 21
  23 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 23 150
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 23 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 23 150 (accept_3_4 19 23 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  23 150 (Polychromatic418967fa.accept_19_18_4_17_1_2618 18 23 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 23 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 23 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 150 (accept_3_4 16 23 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 23 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 150
  (Polychromatic418967fa.accept_21_14_2_3_1_8019 14 23 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 150 (accept_3_4 13 23 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 150 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 23 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 150 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 23 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 150 (accept_3_4 10 23 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 23 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 150
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 23 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 150 (accept_3_4 7 23 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  150 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 23 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 23 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 150 (accept_3_4 4 23 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 23 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 150 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  23 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 150 (accept_3_4 1 23 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 150))))))))))))))))))))))) (allB_succ 22 150
  (allA_succ_of_accept 21 22 150 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 22 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 22 150 2 10 11 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 22 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 19
  22 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 150 2 9 11 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 150 (accept_3_5 17
  22 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 22 150 2 8 11 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 22 150
  (Polychromatic418967fa.accept_12_3_10_6_1_442 15 22 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 22 150 2 7 11 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 22 150 (Polychromatic418967fa.accept_20_13_2_10_1_2301 13 22 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 150 2 6 11 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 150 (accept_3_5 11 22 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 22 150 2 5 11 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 22 150 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 22 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 22 150 2 4 11 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 22 150 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 22
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 150 2 3 11 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 150 (accept_3_5 5 22
  150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 22 150 2 2 11 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 22 150
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 22 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 22 150 2 1 11 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 22 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 22 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 22 150)))))))))))))))))))))) (allB_succ 21 150 (allA_succ_of_accept 20 21
  150 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 21 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 21 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 150 3 6 7 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 150 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 21 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 150
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 21 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 21 150 3 5 7 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 21 150 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 21 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 150 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 21 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 21 150 3 4 7 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 21 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 21 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 150 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 21 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 150 3 3 7 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 150 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 21 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 21 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 21 150 3 2 7 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 21 150 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 21 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 150 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 21 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 21 150 3 1 7 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 21 150
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 21 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 21 150 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 21 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 21 150))))))))))))))))))))) (allB_succ 20 150 (allA_succ_of_accept 19 20 150
  (accept_3_4 19 20 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 150 2 9 10 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 150
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 20 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 150 2 8 10 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 20 150 5 3 4 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 20 150 2 7 10 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 20 150 (accept_3_4 13 20 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 20
  150 2 6 10 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  20 150 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 20 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 20 150 10 1 2 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 20 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 20 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 20 150 2 4 10 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 20 150 (accept_3_4 7 20 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 150 2 3 10 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 5 20 150 5 1 4 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 4 20 150 2 2 10 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 20 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 20 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 150 2 1 10 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 150 (accept_3_4 1 20 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 20 150)))))))))))))))))))) (allB_succ 19 150 (allA_succ_of_accept 18 19 150
  (Polychromatic418967fa.accept_16_2_3_6_1_3372 18 19 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 150 (accept_3_5 17 19 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 19 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 19 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 150 (accept_3_5 14 19 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 19 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 150
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 19 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 150 (accept_3_5 11 19 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 150 (Polychromatic418967fa.accept_26_10_19_20_1_8018 10 19 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 19 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 150 (accept_3_5 8 19 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 150 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 19 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 150
  (Polychromatic418967fa.accept_20_6_19_10_1_3523 6 19 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 150 (accept_3_5 5 19 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  150 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 19 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 150 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 19 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 150 (accept_3_5 2 19 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 19 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 150))))))))))))))))))) (allB_succ 18 150 (allA_succ_of_accept 17
  18 150 (Polychromatic418967fa.accept_16_1_2_6_1_2295 17 18 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 18 150 2 8 9 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 18 150 3 5 6 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 18 150 2 7 9 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 18 150 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 18 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 150 6 2 3 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 150 (Polychromatic418967fa.accept_13_11_5_7_1_2420
  11 18 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 18 150 2 5 9 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 18 150 3 3 6 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 18 150 2 4 9 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 150
  (Polychromatic418967fa.accept_14_7_4_10_1_1351 7 18 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 18 150 6 1 3 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 18 150 (Polychromatic418967fa.accept_19_5_18_17_1_8017 5 18 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 150 2 2 9 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 18 150 3 1 6 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 18 150 2 1 9 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 18 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 150)))))))))))))))))) (allB_succ 17 150
  (allA_succ_of_accept 16 17 150 (accept_3_4 16 17 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  17 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 17 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 17 150 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 17 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 150 (accept_3_4 13 17 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 17 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 17 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 17 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 150 (accept_3_4 10 17 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  17 150 (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 17 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 17 150 (Polychromatic418967fa.accept_20_8_17_10_1_8016 8 17 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 150 (accept_3_4 7 17 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 150 (Polychromatic418967fa.accept_13_6_4_7_1_2464 6 17 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 150
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 17 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 150 (accept_3_4 4 17 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17
  150 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 17 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 17 150 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 17 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 150 (accept_3_4 1 17 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 17 150))))))))))))))))) (allB_succ 16 150 (allA_succ_of_accept 15 16 150
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 16 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 150 2 7 8 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 16 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 150 2 6 8 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 150 (accept_3_5 11 16 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 150 2 5 8 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 150 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 16 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 150 2 4 8 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 150 (Polychromatic418967fa.accept_19_7_16_17_1_6567
  7 16 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 150 2 3 8 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 150 (accept_3_5 5 16
  150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 150 2 2 8 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 150
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 16 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 150 2 1 8 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 16 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 150)))))))))))))))) (allB_succ 15 150 (allA_succ_of_accept 14 15 150
  (Polychromatic418967fa.accept_11_3_4_7_1_114 14 15 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 15 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 150 3 4 5 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 15 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 15 150 5 2 3 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 15 150 3 3 5 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 15 150
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 8 15 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 150 (Polychromatic418967fa.accept_16_7_15_6_1_1428 7 15 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 150 3 2 5 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 15 150 5 1 3 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 15 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 15 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 150 3 1 5 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 150
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 15 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 15 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 15 150))))))))))))))) (allB_succ 14 150 (allA_succ_of_accept 13 14 150
  (accept_3_4 13 14 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 150 2 6 7 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 150
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 14 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 14 150 2 5 7 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 14 150 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 14 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 150 2 4 7 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 14 150 (accept_3_4 7 14 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 14 150 2 3 7 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 14 150 (Polychromatic418967fa.accept_19_5_14_17_1_6550 5 14 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 150 2 2 7 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 14
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 150 2 1 7 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 150 (accept_3_4 1 14
  150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 150)))))))))))))) (allB_succ 13 150 (allA_succ_of_accept 12
  13 150 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 13 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 13 150 (accept_3_5 11 13 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 13 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 13 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 13 150 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 13 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 150 (accept_3_5 8 13 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 13
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 150
  (Polychromatic418967fa.accept_19_6_13_17_1_8015 6 13 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 150 (accept_3_5 5 13 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  150 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 13 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 13 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 150 (accept_3_5 2 13 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 13 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 150))))))))))))) (allB_succ 12 150 (allA_succ_of_accept 11 12
  150 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 12 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 12 150 2 5 6 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 12 150 3 3 4 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 12 150 2 4 6 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 12 150 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 12 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 150 6 1 2 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 150 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 12 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 150 2 2 6 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 12 150 3 1 4 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 12 150 2 1 6 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 150
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 12 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 150)))))))))))) (allB_succ 11 150 (allA_succ_of_accept 10 11 150 (accept_3_4 10 11 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 11 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 150
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 11 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 11 150 (accept_3_4 7 11 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11
  150 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 11 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 11 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 11 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 150 (accept_3_4 4 11 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 11 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 11 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 150 (Polychromatic418967fa.accept_16_2_11_6_1_737 2
  11 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 150 (accept_3_4 1 11 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 150))))))))))) (allB_succ 10 150 (allA_succ_of_accept 9 10 150
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 10 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 10 150 2 4 5 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 10 150 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 10 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 10 150 2 3 5 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 10 150 5 1 2 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 10 150 2 2 5 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 10 150 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 10 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 10 150 2 1 5 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 10 150
  (Polychromatic418967fa.accept_17_1_10_14_1_1173 1 10 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 10 150)))))))))) (allB_succ 9 150 (allA_succ_of_accept 8 9 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 8
  9 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 9 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 9 150 3 2 3 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 9 150 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 9 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 150 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 9 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 9 150 3 1 3 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 9 150
  (Polychromatic418967fa.accept_11_2_9_7_1_124 2 9 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 9 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 9 150))))))))) (allB_succ 8 150 (allA_succ_of_accept 7 8 150 (accept_3_4 7 8
  150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 8 150 2 3 4 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 8 150
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 8 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 8 150 2 2 4 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 8 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 8 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 150 2 1 4 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 150 (accept_3_4 1 8 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 150)))))))) (allB_succ 7 150 (allA_succ_of_accept 6 7 150
  (Polychromatic418967fa.accept_17_6_7_14_1_6704 6 7 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 150 (accept_3_5 5 7 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 150
  (Polychromatic418967fa.accept_9_4_7_6_1_255 4 7 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 150 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 7 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 150 (accept_3_5 2 7 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 7 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 150))))))) (allB_succ 6 150 (allA_succ_of_accept 5 6 150
  (Polychromatic418967fa.accept_20_5_6_10_1_3536 5 6 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 6 150 2 2 3 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 6 150 3 1 2 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 6 150 2 1 3 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 150 (Polychromatic418967fa.accept_11_1_6_7_1_116 1 6 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 150)))))) (allB_succ 5 150 (allA_succ_of_accept 4 5 150 (accept_3_4 4 5
  150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 3
  5 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 150
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 5 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 150 (accept_3_4 1 5 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 150)))))
  (allB_succ 4 150 (allA_succ_of_accept 3 4 150 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 4 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 150 2 1 2 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 4
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 4 150)))) (allB_succ 3 150
  (allA_succ_of_accept 2 3 150 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 3 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 3 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 150))) (allB_succ 2 150 (allA_succ_of_accept
  1 2 150 (accept_3_4 1 2 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 150)) (allB_two
  150)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


