-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch162_Segment000
-- name    : Polychromatic418967fa_Branch162_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:27:06.651192+00:00
-- url     : https://prove2.me/theorems/2022b4f1-c550-4b94-a18f-55f4df1bc93f
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

def Polychromatic418967fa.branch_162_segment_000 : allB 107 162 :=
  allB_succ' 57 106 162 (Eq.refl Bool.true) (allA_succ_of_gcd 56 106 162 2 28 53 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 106 162
  (Polychromatic418967fa.accept_23_9_14_1_1_8977 55 106 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 106 162 2 27 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 106 162 (accept_3_5 53 106 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 106 162 2 26 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 106 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 51 106 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 106 162 2 25 53 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 106 162
  (Polychromatic418967fa.accept_13_10_2_6_1_1044 49 106 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 106 162 2 24 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 106 162 (accept_3_5 47 106 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 106 162 2 23 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 106 162 (Polychromatic418967fa.accept_12_9_10_6_1_872 45 106 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 106 162 2 22 53 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 106 162
  (Polychromatic418967fa.accept_13_4_2_6_1_1043 43 106 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 106 162 2 21 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 106 162 (accept_3_5 41 106 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 106 162 2 20 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 106 162 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 106 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 106 162 2 19 53 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 106 162
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 37 106 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 106 162 2 18 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 106 162 (accept_3_5 35 106 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 106 162 2 17 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 106 162 (Polychromatic418967fa.accept_12_9_10_6_1_872 33 106 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 106 162 2 16 53 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 106 162
  (Polychromatic418967fa.accept_10_1_6_2_1_867 31 106 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 106 162 2 15 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 106 162 (accept_3_5 29 106 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 106 162 2 14 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 106 162 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 106 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 106 162 2 13 53 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 106 162
  (Polychromatic418967fa.accept_13_12_2_6_1_2396 25 106 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 106 162 2 12 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 106 162 (accept_3_5 23 106 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 106 162 2 11 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 106 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 106 162 2 10 53 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 162
  (Polychromatic418967fa.accept_15_4_1_12_1_914 19 106 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 106 162 2 9 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 106 162 (accept_3_5 17 106 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  106 162 2 8 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 106 162 (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 106 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 106 162 2 7 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 106 162 (Polychromatic418967fa.accept_15_13_1_12_1_1638 13 106 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 106 162 2 6 53 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 106 162 (accept_3_5 11
  106 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 106 162 2 5 53 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 106 162
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 106 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 106 162 2 4 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 106 162 (Polychromatic418967fa.accept_21_7_1_15_1_680 7 106 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 106 162 2 3 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 106 162 (accept_3_5 5 106 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 106 162 2 2 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 106 162 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 106 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 106 162 2 1 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 106 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 1
  106 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  162))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 105 162 (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 105 162 3 19 35 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 105 162 (Polychromatic418967fa.accept_12_8_9_6_1_127 56 105 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 55
  105 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 105 162 3 18 35 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 105 162
  (Polychromatic418967fa.accept_10_3_5_2_1_38 53 105 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 105 162 (Polychromatic418967fa.accept_12_4_9_6_1_440 52 105 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 105 162 3 17 35 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 105 162 (Polychromatic418967fa.accept_12_2_9_6_1_439
  50 105 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 162
  (Polychromatic418967fa.accept_16_1_9_2_1_4161 49 105 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 105 162 3 16 35 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 105 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 105 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 162
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 46 105 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 105 162 3 15 35 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 105 162 (Polychromatic418967fa.accept_12_8_9_6_1_127 44 105 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 43
  105 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 105 162 3 14 35 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 105 162
  (Polychromatic418967fa.accept_13_2_1_6_1_2365 41 105 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 105 162 (Polychromatic418967fa.accept_12_4_9_6_1_440 40 105 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 105 162 3 13 35 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 105 162 (Polychromatic418967fa.accept_10_8_5_2_1_881
  38 105 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 162
  (Polychromatic418967fa.accept_10_7_5_2_1_880 37 105 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 105 162 3 12 35 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 105 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 105 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 105 162
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 34 105 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 105 162 3 11 35 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 105 162 (Polychromatic418967fa.accept_12_8_9_6_1_127 32 105 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  105 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 105 162 3 10 35 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 105 162
  (Polychromatic418967fa.accept_13_3_1_6_1_509 29 105 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 105 162 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 105 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 105 162 3 9 35 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 105 162 (Polychromatic418967fa.accept_12_2_9_6_1_439
  26 105 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 162
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 25 105 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 105 162 3 8 35 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 105 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 105 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 162 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 105
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 105 162 3 7 35 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 105 162
  (Polychromatic418967fa.accept_12_8_9_6_1_127 20 105 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 105 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 105 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 105 162 3 6 35 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 105 162 (Polychromatic418967fa.accept_10_7_5_2_1_880
  17 105 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 162
  (Polychromatic418967fa.accept_12_4_9_6_1_440 16 105 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 105 162 3 5 35 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 105 162 (Polychromatic418967fa.accept_11_3_6_8_1_1924 14 105 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 162 (Polychromatic418967fa.accept_10_3_5_2_1_38 13 105 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 105 162 3 4 35 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 105 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 105 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 105 162 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 105 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 105 162 3 3 35 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 105 162 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 105 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 105 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 105 162 3 2 35 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 105 162 (Polychromatic418967fa.accept_13_5_1_6_1_2367 5 105 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 162 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 105 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 105 162 3 1 35 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 105 162
  (Polychromatic418967fa.accept_12_2_9_6_1_439 2 105 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 162 (Polychromatic418967fa.accept_14_1_7_8_1_2063 1 105 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 105 162))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 59 104 162 (Eq.refl Bool.true) (allA_succ_of_gcd 58 104 162 2 29 52 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 104 162
  (Polychromatic418967fa.accept_10_7_4_2_1_903 57 104 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 104 162 2 28 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 104 162 (accept_3_4 55 104 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 104 162 2 27 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 104 162 (Polychromatic418967fa.accept_19_15_9_10_1_4615 53 104 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 162 2 26 52 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 162
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 104 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 104 162 2 25 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 104 162 (accept_3_4 49 104 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 104 162 2 24 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 104 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 104 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 104 162 2 23 52 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 104 162
  (Polychromatic418967fa.accept_12_9_8_6_1_466 45 104 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 104 162 2 22 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 104 162 (accept_3_4 43 104 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 104 162 2 21 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 104 162 (Polychromatic418967fa.accept_15_11_14_12_1_2458 41 104 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 104 162 2 20 52 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 104 162
  (Polychromatic418967fa.accept_12_3_8_6_1_895 39 104 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 104 162 2 19 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 104 162 (accept_3_4 37 104 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 104 162 2 18 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 104 162 (Polychromatic418967fa.accept_11_2_5_8_1_470 35 104 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 104 162 2 17 52 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 104 162
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 104 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 104 162 2 16 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 104 162 (accept_3_4 31 104 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 104 162 2 15 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 104 162 (Polychromatic418967fa.accept_20_9_4_2_1_1900 29 104 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 104 162 2 14 52 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 104 162
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 104 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 104 162 2 13 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 104 162 (accept_3_4 25 104 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 104 162 2 12 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 104 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 104 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 162 2 11 52 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 162
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 104 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 104 162 2 10 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 104 162 (accept_3_4 19 104 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 104 162 2 9 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 104 162 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 104 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 104 162 2 8 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 104 162 (Polychromatic418967fa.accept_12_3_8_6_1_895
  15 104 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 162 2 7 52 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 104 162
  (accept_3_4 13 104 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 104 162 2 6 52 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 162
  (Polychromatic418967fa.accept_15_11_14_12_1_2458 11 104 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 104 162 2 5 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 104 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 104 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 104 162 2 4 52 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 104 162 (accept_3_4 7 104 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 104 162 2 3 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 104 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 104 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 104 162 2 2 52 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 104 162
  (Polychromatic418967fa.accept_11_3_5_8_1_458 3 104 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 104 162 2 1 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 104 162 (accept_3_4 1 104 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  162))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 103 162 (Eq.refl Bool.true)
  (allA_succ_of_accept 59 103 162 (accept_3_5 59 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 103 162 (Polychromatic418967fa.accept_20_18_3_2_1_5929 58 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 103 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 103 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 103 162 (accept_3_5 56 103 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 103 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 103 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 103 162
  (Polychromatic418967fa.accept_13_2_12_6_1_2394 54 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 103 162 (accept_3_5 53 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 103 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 103 162 (Polychromatic418967fa.accept_10_1_3_2_1_220 51 103 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 103 162 (accept_3_5 50 103 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 103 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 103 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 103 162
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 103 162 (accept_3_5 47 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 103 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 103 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 103 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 103 162 (accept_3_5 44 103 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 103 162 (Polychromatic418967fa.accept_16_11_7_2_1_4185 43 103 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 103 162
  (Polychromatic418967fa.accept_17_8_1_9_1_7738 42 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 103 162 (accept_3_5 41 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 103 162 (Polychromatic418967fa.accept_11_7_4_8_1_1371 40 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 103 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 103 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 103 162 (accept_3_5 38 103 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 103 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 103 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 103 162
  (Polychromatic418967fa.accept_13_10_12_6_1_991 36 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 103 162 (accept_3_5 35 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 103 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 103 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 103 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 103 162 (accept_3_5 32 103 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 103 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 103 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 103 162
  (Polychromatic418967fa.accept_19_11_8_10_1_8901 30 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 103 162 (accept_3_5 29 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 103 162 (Polychromatic418967fa.accept_13_2_12_6_1_2394 28 103 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 103 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 103 162 (accept_3_5 26 103 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 103 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 25
  103 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 103 162
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 103 162 (accept_3_5 23 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 103 162 (Polychromatic418967fa.accept_21_1_19_15_1_8914 22 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 103 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 103 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 103 162 (accept_3_5 20 103 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 103 162 (Polychromatic418967fa.accept_20_19_3_2_1_3118 19 103 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 162
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 103 162 (accept_3_5 17 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 103 162 (Polychromatic418967fa.accept_15_1_13_12_1_347 16 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 103 162 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 103 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 103 162 (accept_3_5 14 103 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 103 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 103 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 103 162
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 103 162 (accept_3_5 11 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 103 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 103 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 103 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 162 (accept_3_5 8 103 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 162 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 103 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 162
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 103 162 (accept_3_5 5 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  103 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 103 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 103 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 103 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 162 (accept_3_5 2 103 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 103 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103
  162)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 102 162 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 102 162 6 10 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 102 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 102 162 2 29 51 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 102 162 3 19 34 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 102 162 2 28 51 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 102 162
  (Polychromatic418967fa.accept_19_17_7_10_1_1171 55 102 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 102 162 6 9 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 102 162 (Polychromatic418967fa.accept_14_11_4_8_1_664 53 102 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 102 162 2 26 51 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 102 162 3 17 34 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 102 162 2 25 51 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 102 162
  (Polychromatic418967fa.accept_11_5_3_8_1_454 49 102 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 162 6 8 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 102 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 102 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 102 162 2 23 51 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 102 162 3 15 34 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 102 162 2 22 51 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 102 162
  (Polychromatic418967fa.accept_13_4_11_6_1_1033 43 102 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 162 6 7 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 102 162 (Polychromatic418967fa.accept_16_9_6_2_1_3101 41 102 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 162 2 20 51 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 102 162 3 13 34 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 102 162 2 19 51 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 102 162
  (Polychromatic418967fa.accept_19_18_7_10_1_9001 37 102 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 102 162 6 6 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 102 162 (Polychromatic418967fa.accept_16_3_6_2_1_4157 35 102 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 162 2 17 51 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 102 162 3 11 34 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 102 162 2 16 51 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 162
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 102 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 162 6 5 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 102 162 (Polychromatic418967fa.accept_21_8_18_15_1_5812 29 102 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 162 2 14 51 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 102 162 3 9 34 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 102 162 2 13 51 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 162
  (Polychromatic418967fa.accept_14_11_4_8_1_664 25 102 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 162 6 4 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 102 162 (Polychromatic418967fa.accept_21_2_18_15_1_4236 23 102 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 162 2 11 51 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 102 162 3 7 34 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 102 162 2 10 51 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 162
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 102 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 162 6 3 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 102 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 162 2 8 51 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 102 162 3 5 34 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 102 162 2 7 51 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 162
  (Polychromatic418967fa.accept_21_13_18_15_1_2837 13 102 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 102 162 6 2 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 102 162 (Polychromatic418967fa.accept_14_11_4_8_1_664 11 102 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 162 2 5 51 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 102 162 3 3 34 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 102 162 2 4 51 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 162
  (Polychromatic418967fa.accept_21_7_18_15_1_2887 7 102 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 102 162 6 1 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 102 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 102 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102 162 2 2 51 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 102 162 3 1 34 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 102 162 2 1 51 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 162 (Polychromatic418967fa.accept_16_1_6_2_1_3100 1 102 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  162))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 101 162 (Eq.refl Bool.true)
  (allA_succ_of_accept 61 101 162 (accept_3_4 61 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 101 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 101 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 101 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 101 162 (accept_3_4 58 101 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 101 162 (Polychromatic418967fa.accept_13_5_10_6_1_2361 57 101 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 101 162
  (Polychromatic418967fa.accept_10_6_1_2_1_874 56 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 101 162 (accept_3_4 55 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 101 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 101 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 101 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 101 162 (accept_3_4 52 101 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 101 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 101 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 101 162
  (Polychromatic418967fa.accept_19_12_6_10_1_9000 50 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 101 162 (accept_3_4 49 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 101 162 (Polychromatic418967fa.accept_13_9_10_6_1_1028 48 101 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 101 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 162 (accept_3_4 46 101 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 162
  (Polychromatic418967fa.accept_16_13_5_2_1_2131 45 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 101 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 101 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 162 (accept_3_4 43 101 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 101 162 (Polychromatic418967fa.accept_13_3_10_6_1_2382 42 101 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 162
  (Polychromatic418967fa.accept_13_2_10_6_1_1676 41 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 101 162 (accept_3_4 40 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 101 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 101 162 (Polychromatic418967fa.accept_11_5_2_8_1_866 38 101 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 101 162 (accept_3_4 37 101 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 101 162 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 101
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 101 162 (accept_3_4 34 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 101 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 101 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 101 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 162 (accept_3_4 31 101 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 101 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 101 162
  (Polychromatic418967fa.accept_10_9_1_2_1_522 29 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 101 162 (accept_3_4 28 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 101 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 101 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 101 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 162 (accept_3_4 25 101 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 101 162 (Polychromatic418967fa.accept_21_3_17_15_1_4199 24 101 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 101 162 (accept_3_4 22 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 101 162 (Polychromatic418967fa.accept_19_2_6_10_1_3364 21 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 101 162 (Polychromatic418967fa.accept_19_1_6_10_1_3366 20 101 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 162 (accept_3_4 19 101 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 101 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 101 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 162
  (Polychromatic418967fa.accept_13_4_10_6_1_989 17 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 101 162 (accept_3_4 16 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 101 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 101 162 (Polychromatic418967fa.accept_15_14_11_12_1_4440 14 101 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 162 (accept_3_4 13 101 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 101 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 101 162 (accept_3_4 10 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  101 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 101 162 (Polychromatic418967fa.accept_15_8_11_12_1_1626 8 101 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 162 (accept_3_4 7 101 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 162 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 101 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 162
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 162 (accept_3_4 4 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 101 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 101 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 162 (accept_3_4 1 101 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 101 162)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63
  100 162 (Eq.refl Bool.true) (allA_succ_of_gcd 62 100 162 2 31 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 100 162 (Polychromatic418967fa.accept_26_9_22_6_1_8999 61 100
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 100 162 2 30 50 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 100 162 (accept_3_5 59
  100 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 100 162 2 29 50 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 100 162
  (Polychromatic418967fa.accept_12_9_4_6_1_460 57 100 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 100 162 2 28 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 100 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 100 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 100 162 2 27 50 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 100 162 (accept_3_5 53 100 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 100 162 2 26 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 100 162 (Polychromatic418967fa.accept_12_3_4_6_1_434
  51 100 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 100 162 2 25 50 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 100 162
  (Polychromatic418967fa.accept_13_10_9_6_1_1026 49 100 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 100 162 2 24 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 100 162 (accept_3_5 47 100 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 100 162 2 23 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 100 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 100 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 100 162 2 22 50 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 100 162
  (Polychromatic418967fa.accept_13_4_9_6_1_2376 43 100 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 100 162 2 21 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 100 162 (accept_3_5 41 100 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 100 162 2 20 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 100 162 (Polychromatic418967fa.accept_12_3_4_6_1_434 39 100 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 100 162 2 19 50 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 100 162
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 37 100 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 100 162 2 18 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 100 162 (accept_3_5 35 100 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 100 162 2 17 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 100 162 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 100 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 100 162 2 16 50 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 100 162
  (Polychromatic418967fa.accept_7_3_2_1_1_225 31 100 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 100 162 2 15 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 100 162 (accept_3_5 29 100 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 100 162 2 14 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 100 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 100 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 100 162 2 13 50 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 100 162
  (Polychromatic418967fa.accept_23_2_8_1_1_8998 25 100 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 100 162 2 12 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 100 162 (accept_3_5 23 100 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 100 162 2 11 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 100 162 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 100 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 100 162 2 10 50 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 100 162
  (Polychromatic418967fa.accept_39_19_22_6_1_8997 19 100 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 100 162 2 9 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 100 162 (accept_3_5 17 100 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 100 162 2 8 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 100 162 (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 100 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 100 162 2 7 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 100 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 13
  100 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 100 162 2 6 50 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 100 162 (accept_3_5 11
  100 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 100 162 2 5 50 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 100 162
  (Polychromatic418967fa.accept_12_9_4_6_1_460 9 100 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 100 162 2 4 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 100 162 (Polychromatic418967fa.accept_13_7_9_6_1_148 7 100 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 100 162 2 3 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 100 162 (accept_3_5 5 100 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 100 162 2 2 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 100 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 100 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 100 162 2 1 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 100 162 (Polychromatic418967fa.accept_13_1_9_6_1_146 1
  100 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100
  162))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 99 162 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 99 162 9 7 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 99 162 (Polychromatic418967fa.accept_12_2_3_6_1_112 62 99 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 99 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 99 162 3 20 33 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 99 162
  (Polychromatic418967fa.accept_15_14_9_12_1_2498 59 99 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 99 162 (Polychromatic418967fa.accept_12_10_3_6_1_882 58 99 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 99 162 3 19 33 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 99 162 (Polychromatic418967fa.accept_12_8_3_6_1_909 56
  99 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 99 162
  (Polychromatic418967fa.accept_15_10_9_12_1_2497 55 99 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 99 162 9 6 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 99 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 99 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 162 (Polychromatic418967fa.accept_12_4_3_6_1_879 52 99 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 99 162 3 17 33 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 99 162
  (Polychromatic418967fa.accept_12_2_3_6_1_112 50 99 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 99 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 99 162 3 16 33 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 99 162 (Polychromatic418967fa.accept_10_7_9_2_1_1887
  47 99 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 162
  (Polychromatic418967fa.accept_12_10_3_6_1_882 46 99 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 99 162 9 5 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 99 162 (Polychromatic418967fa.accept_12_8_3_6_1_909 44 99 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 162 (Polychromatic418967fa.accept_20_3_19_2_1_5926 43 99
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 99 162 3 14 33 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 99 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 99 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 99 162 (Polychromatic418967fa.accept_12_4_3_6_1_879 40 99 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 99 162 3 13 33 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 99 162 (Polychromatic418967fa.accept_12_2_3_6_1_112 38
  99 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 37 99 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 99 162 9 4 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 99 162 (Polychromatic418967fa.accept_14_7_1_8_1_2873 35 99 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 162 (Polychromatic418967fa.accept_12_10_3_6_1_882 34 99 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 99 162 3 11 33 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 99 162
  (Polychromatic418967fa.accept_12_8_3_6_1_909 32 99 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 162 (Polychromatic418967fa.accept_10_1_9_2_1_45 31 99 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 99 162 3 10 33 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 99 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 99
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 162
  (Polychromatic418967fa.accept_12_4_3_6_1_879 28 99 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 99 162 9 3 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 99 162 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 99 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 99 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 99 162 3 8 33 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 99 162
  (Polychromatic418967fa.accept_14_9_1_8_1_2849 23 99 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 99 162 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 99 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 99 162 3 7 33 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 99 162 (Polychromatic418967fa.accept_12_8_3_6_1_909 20 99 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 162
  (Polychromatic418967fa.accept_15_4_9_12_1_2495 19 99 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 99 162 9 2 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 99 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 99 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 162 (Polychromatic418967fa.accept_12_4_3_6_1_879 16 99 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 99 162 3 5 33 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 99 162
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 99 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 99 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 99 162 3 4 33 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 99 162 (Polychromatic418967fa.accept_10_1_9_2_1_45 11 99 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 162
  (Polychromatic418967fa.accept_12_10_3_6_1_882 10 99 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 99 162 9 1 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 99 162 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 99 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 162 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 99 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 99 162 3 2 33 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 99 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 99 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 99 162 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 99 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 99 162 3 1 33 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 99 162 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 99 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 99 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 99 162)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 98 162 (Eq.refl
  Bool.true) (allA_succ_of_gcd 64 98 162 2 32 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 98 162 (Polychromatic418967fa.accept_12_3_2_6_1_138 63 98 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 98 162 2 31 49 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 98 162 (accept_3_4 61 98 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 98 162 2 30 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 98 162
  (Polychromatic418967fa.accept_21_17_14_15_1_5750 59 98 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 98 162 2 29 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 98 162 (Polychromatic418967fa.accept_12_9_2_6_1_455 57 98 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 98 162 2 28 49 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 98 162 (accept_3_4 55 98 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 98 162 2 27 49 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 98 162
  (Polychromatic418967fa.accept_11_9_10_8_1_444 53 98 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 98 162 2 26 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 98 162 (Polychromatic418967fa.accept_12_3_2_6_1_138 51 98 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 98 162 2 25 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 98 162 (accept_3_4 49 98 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 98 162 2 24 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 98 162 (Polychromatic418967fa.accept_19_9_3_10_1_6017 47 98 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 98 162 2 23 49 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 98 162
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 98 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 98 162 2 22 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 98 162 (accept_3_4 43 98 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 98
  162 2 21 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  98 162 (Polychromatic418967fa.accept_15_11_8_12_1_4437 41 98 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 98 162 2 20 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 98 162 (Polychromatic418967fa.accept_12_3_2_6_1_138 39 98 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 98 162 2 19 49 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 98 162 (accept_3_4 37 98 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 98 162 2 18 49 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 98 162
  (Polychromatic418967fa.accept_10_5_8_2_1_517 35 98 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 98 162 2 17 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 98 162 (Polychromatic418967fa.accept_12_9_2_6_1_455 33 98 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 98 162 2 16 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 98 162 (accept_3_4 31 98 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 98 162 2 15 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 98 162 (Polychromatic418967fa.accept_21_8_14_15_1_5777 29 98
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 98 162 2 14 49 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 98 162
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 98 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 98 162 2 13 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 98 162 (accept_3_4 25 98 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 98
  162 2 12 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  98 162 (Polychromatic418967fa.accept_20_3_18_2_1_5918 23 98 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 98 162 2 11 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 98 162 (Polychromatic418967fa.accept_12_9_2_6_1_455 21 98 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 98 162 2 10 49 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 98 162 (accept_3_4 19 98 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 98 162 2 9 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 98 162 (Polychromatic418967fa.accept_13_4_7_6_1_2359
  17 98 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 98 162 2 8 49 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 98 162
  (Polychromatic418967fa.accept_10_5_8_2_1_517 15 98 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 98 162 2 7 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 98 162 (accept_3_4 13 98 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98
  162 2 6 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  98 162 (Polychromatic418967fa.accept_15_11_8_12_1_4437 11 98 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 98 162 2 5 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 98 162 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 98 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 162 2 4 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 98 162 (accept_3_4 7 98 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 98 162 2 3 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 98 162 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 98 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 98 162 2 2 49 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 98 162
  (Polychromatic418967fa.accept_12_3_2_6_1_138 3 98 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 98 162 2 1 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 98 162 (accept_3_4 1 98 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  162))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 97 162 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 97 162 (accept_3_5 65 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  97 162 (Polychromatic418967fa.accept_10_4_7_2_1_211 64 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 97 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 97 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 97 162 (accept_3_5 62 97 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 97 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 97 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 97 162
  (Polychromatic418967fa.accept_16_12_1_2_1_2163 60 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 97 162 (accept_3_5 59 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  97 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 58 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 97 162 (Polychromatic418967fa.accept_16_9_1_2_1_2126 57 97 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 97 162 (accept_3_5 56 97 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 97 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 97 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 162
  (Polychromatic418967fa.accept_7_5_6_1_1_407 54 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 97 162 (accept_3_5 53 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  97 162 (Polychromatic418967fa.accept_20_12_17_2_1_8961 52 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 97 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 97 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 162 (accept_3_5 50 97 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 162 (Polychromatic418967fa.accept_10_9_7_2_1_887 49 97 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 162
  (Polychromatic418967fa.accept_15_3_7_12_1_372 48 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 162 (accept_3_5 47 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 162 (Polychromatic418967fa.accept_19_8_2_10_1_7415 46 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 162 (Polychromatic418967fa.accept_10_5_7_2_1_516 45 97 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 162 (accept_3_5 44 97 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 97 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 162
  (Polychromatic418967fa.accept_23_19_5_1_1_8996 42 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 162 (accept_3_5 41 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 97 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 162 (accept_3_5 38 97 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 97 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 162
  (Polychromatic418967fa.accept_15_6_7_12_1_869 36 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 162 (accept_3_5 35 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 162 (Polychromatic418967fa.accept_10_4_7_2_1_211 34 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 97 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 162 (accept_3_5 32 97 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 97 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 162
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 162 (accept_3_5 29 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 162 (Polychromatic418967fa.accept_16_12_1_2_1_2163 28 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 97 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 162 (accept_3_5 26 97 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 162 (Polychromatic418967fa.accept_10_5_7_2_1_516 25 97 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 162
  (Polychromatic418967fa.accept_10_4_7_2_1_211 24 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 162 (accept_3_5 23 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 162 (Polychromatic418967fa.accept_16_6_1_2_1_3129 22 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 162 (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 97 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 162 (accept_3_5 20 97 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 97 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 162
  (Polychromatic418967fa.accept_15_3_7_12_1_372 18 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 162 (accept_3_5 17 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 97 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 162 (accept_3_5 14 97 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 162 (Polychromatic418967fa.accept_19_13_2_10_1_7416 13 97 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 162
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 162 (accept_3_5 11 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 162 (Polychromatic418967fa.accept_11_10_9_8_1_1974 10 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 97 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 162 (accept_3_5 8 97 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 97 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 162
  (Polychromatic418967fa.accept_15_6_7_12_1_869 6 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 162 (accept_3_5 5 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  162 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 97 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 97 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 162 (accept_3_5 2 97 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 162 (Polychromatic418967fa.accept_22_1_9_8_1_8995 1 97 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  162)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 96 162 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 96 162 6 11 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 96 162 (Polychromatic418967fa.accept_15_5_6_12_1_916 65 96 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 96 162 2 32 48 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 96 162 3 21 32 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 96 162 2 31 48 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 96 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 61
  96 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 96 162 6 10 16 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 96 162
  (Polychromatic418967fa.accept_7_3_5_1_1_72 59 96 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 96 162 2 29 48 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 96 162 3 19 32 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 56 96 162 2 28 48 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 96 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 96 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 162 6 9 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 96 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 96 162 2 26 48 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 96 162 3 17 32 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 96 162 2 25 48 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 96 162
  (Polychromatic418967fa.accept_13_10_5_6_1_1671 49 96 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 96 162 6 8 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 96 162 (Polychromatic418967fa.accept_15_2_6_12_1_1613 47 96 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96 162 2 23 48 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 96 162 3 15 32 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 96 162 2 22 48 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 96 162 (Polychromatic418967fa.accept_13_4_5_6_1_3201
  43 96 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96 162 6 7 16 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 96 162
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 96 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 96 162 2 20 48 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 96 162 3 13 32 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 96 162 2 19 48 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 96 162 (Polychromatic418967fa.accept_13_11_5_6_1_519 37 96 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 162 6 6 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 162 (Polychromatic418967fa.accept_15_5_6_12_1_916 35 96 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96 162 2 17 48 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 96 162 3 11 32 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 96 162 2 16 48 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 96 162
  (Polychromatic418967fa.accept_7_3_5_1_1_72 31 96 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 96 162 6 5 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 96 162 (Polychromatic418967fa.accept_13_3_5_6_1_3192 29 96 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96 162 2 14 48 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 96 162 3 9 32 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 96 162 2 13 48 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 25
  96 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 162 6 4 16 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 162
  (Polychromatic418967fa.accept_13_10_5_6_1_1671 23 96 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 96 162 2 11 48 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 96 162 3 7 32 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 96 162 2 10 48 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 96 162 (Polychromatic418967fa.accept_17_2_11_9_1_1739 19 96 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 162 6 3 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 96 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 162 2 8 48 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 96 162 3 5 32 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 96 162 2 7 48 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 162
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 96 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 96 162 6 2 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 96 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 96 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 162 2 5 48 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 96 162 3 3 32 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 96 162 2 4 48 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 96 162 (Polychromatic418967fa.accept_15_7_6_12_1_1614 7 96 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 162 6 1 16 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 162
  (Polychromatic418967fa.accept_15_5_6_12_1_916 5 96 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 96 162 2 2 48 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 96 162 3 1 32 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 96 162 2 1 48 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 96 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 96 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 96 162)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 68 95 162 (Eq.refl Bool.true) (allA_succ_of_accept 67 95 162 (accept_3_4 67 95 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 95 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 162 (accept_3_4 64 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 162 (Polychromatic418967fa.accept_10_3_5_2_1_38 63 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 162 (Polychromatic418967fa.accept_13_10_4_6_1_3224 62 95 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 162 (accept_3_4 61 95 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 162 (Polychromatic418967fa.accept_14_4_11_8_1_2034 60 95
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 162
  (Polychromatic418967fa.accept_7_3_4_1_1_71 59 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 162 (accept_3_4 58 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 162 (Polychromatic418967fa.accept_22_12_7_8_1_8957 56 95 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 162 (accept_3_4 55 95 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 95 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 162 (accept_3_4 52 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 162 (Polychromatic418967fa.accept_15_6_5_12_1_1642 51 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 162 (Polychromatic418967fa.accept_13_11_4_6_1_1006 50 95 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 162 (accept_3_4 49 95 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 162 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 95 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 162
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 162 (accept_3_4 46 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 162 (Polychromatic418967fa.accept_13_5_4_6_1_2371 44 95 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 162 (accept_3_4 43 95 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 162 (Polychromatic418967fa.accept_25_17_20_12_1_8994 42 95 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 162 (accept_3_4 40 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 162 (Polychromatic418967fa.accept_15_9_5_12_1_1640 39 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 95 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 162 (accept_3_4 37 95 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 162 (Polychromatic418967fa.accept_13_10_4_6_1_3224 36 95 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 162
  (Polychromatic418967fa.accept_13_9_4_6_1_1005 35 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 162 (accept_3_4 34 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 162 (Polychromatic418967fa.accept_14_4_11_8_1_2034 32 95 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 162 (accept_3_4 31 95 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 162 (Polychromatic418967fa.accept_17_13_10_9_1_946 30 95
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 162 (accept_3_4 28 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 162 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 95 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 162 (accept_3_4 25 95 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 95 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 162
  (Polychromatic418967fa.accept_10_3_5_2_1_38 23 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 162 (accept_3_4 22 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 162 (Polychromatic418967fa.accept_13_7_4_6_1_3221 20 95 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 162 (accept_3_4 19 95 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 162 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 95 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 162 (accept_3_4 16 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 162 (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 162 (Polychromatic418967fa.accept_25_14_20_12_1_8993 14 95 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 162 (accept_3_4 13 95 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 95 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 162
  (Polychromatic418967fa.accept_13_11_4_6_1_1006 11 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 162 (accept_3_4 10 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 95 162 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 95 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 162 (accept_3_4 7 95 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 95 162 (Polychromatic418967fa.accept_15_6_5_12_1_1642 6 95 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 95
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 95 162 (accept_3_4 4 95 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 95
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 162
  (Polychromatic418967fa.accept_13_2_4_6_1_2356 2 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 95 162 (accept_3_4 1 95 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  162)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 94 162 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 94 162 2 34 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 94 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 67 94 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 94 162 2 33 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 94 162 (accept_3_5 65 94 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 94 162 2 32 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 94 162 (Polychromatic418967fa.accept_12_3_10_6_1_442 63 94 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 94 162 2 31 47 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 94 162
  (Polychromatic418967fa.accept_7_5_3_1_1_424 61 94 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 94 162 2 30 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 94 162 (accept_3_5 59 94 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 94
  162 2 29 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  94 162 (Polychromatic418967fa.accept_10_7_4_2_1_903 57 94 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 94 162 2 28 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 94 162 (Polychromatic418967fa.accept_19_17_18_10_1_7485 55 94 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 94 162 2 27 47 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 94 162 (accept_3_5 53 94 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 94 162 2 26 47 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 94 162
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 94 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 94 162 2 25 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 94 162 (Polychromatic418967fa.accept_13_10_3_6_1_1003 49 94 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 94 162 2 24 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 94 162 (accept_3_5 47 94 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 94 162 2 23 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 94 162 (Polychromatic418967fa.accept_12_9_10_6_1_872 45 94 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 94 162 2 22 47 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 94 162
  (Polychromatic418967fa.accept_19_5_18_10_1_4604 43 94 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 94 162 2 21 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 94 162 (accept_3_5 41 94 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 94
  162 2 20 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  94 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 94 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 94 162 2 19 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 94 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 94 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 94 162 2 18 47 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 94 162 (accept_3_5 35 94 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 94 162 2 17 47 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 94 162
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 94 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 94 162 2 16 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 94 162 (Polychromatic418967fa.accept_13_5_3_6_1_3278 31 94 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 94 162 2 15 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 94 162 (accept_3_5 29 94 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 94 162 2 14 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 94 162 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 94 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 94 162 2 13 47 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 94 162
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 94 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 94 162 2 12 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 94 162 (accept_3_5 23 94 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 94
  162 2 11 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  94 162 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 94 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 94 162 2 10 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 94 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 94 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 94 162 2 9 47 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 94 162 (accept_3_5 17 94 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 94 162 2 8 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 94 162 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 94 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 94 162 2 7 47 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 94 162
  (Polychromatic418967fa.accept_32_13_30_2_1_8992 13 94 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 94 162 2 6 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 94 162 (accept_3_5 11 94 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94
  162 2 5 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  94 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 94 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 94 162 2 4 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 94 162 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 94 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 94 162 2 3 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 94 162 (accept_3_5 5 94 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 94 162 2 2 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 94 162 (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 94 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 94 162 2 1 47 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 162
  (Polychromatic418967fa.accept_13_1_3_6_1_158 1 94 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 94 162))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 93 162 (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 93 162 3 23 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 93 162 (Polychromatic418967fa.accept_11_2_5_8_1_470 68 93 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 93 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 67
  93 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 93 162 3 22 31 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 93 162
  (Polychromatic418967fa.accept_10_5_3_2_1_899 65 93 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 93 162 (Polychromatic418967fa.accept_12_4_9_6_1_440 64 93 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 93 162 3 21 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 93 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 62
  93 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 93 162
  (Polychromatic418967fa.accept_10_1_3_2_1_220 61 93 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 93 162 3 20 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 93 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 93 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 162 (Polychromatic418967fa.accept_11_3_5_8_1_458 58 93 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 93 162 3 19 31 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 93 162
  (Polychromatic418967fa.accept_12_8_9_6_1_127 56 93 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 93 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 93 162 3 18 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 93 162 (Polychromatic418967fa.accept_13_1_2_6_1_515 53
  93 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 162
  (Polychromatic418967fa.accept_7_3_2_1_1_225 52 93 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 93 162 3 17 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 93 162 (Polychromatic418967fa.accept_12_2_9_6_1_439 50 93 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 162 (Polychromatic418967fa.accept_13_10_2_6_1_1044 49 93
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 93 162 3 16 31 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 93 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 93 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 93 162 (Polychromatic418967fa.accept_11_2_5_8_1_470 46 93 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 93 162 3 15 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 93 162 (Polychromatic418967fa.accept_12_8_9_6_1_127 44
  93 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 93 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 93 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 93 162 3 14 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 93 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 93 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 162 (Polychromatic418967fa.accept_12_4_9_6_1_440 40 93 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 93 162 3 13 31 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 93 162
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 93 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 162 (Polychromatic418967fa.accept_15_7_3_12_1_365 37 93 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 93 162 3 12 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 93 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 35
  93 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 162
  (Polychromatic418967fa.accept_7_6_2_1_1_214 34 93 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 93 162 3 11 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 93 162 (Polychromatic418967fa.accept_12_8_9_6_1_127 32 93 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 93 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 93 162 3 10 31 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 93 162
  (Polychromatic418967fa.accept_14_1_9_8_1_2863 29 93 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 93 162 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 93 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 93 162 3 9 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 93 162 (Polychromatic418967fa.accept_12_2_9_6_1_439 26 93 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 162
  (Polychromatic418967fa.accept_10_5_3_2_1_899 25 93 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 93 162 3 8 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 93 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 93 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 162 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 93
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 93 162 3 7 31 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 93 162
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 93 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 93 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 93 162 3 6 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 93 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 93 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 162
  (Polychromatic418967fa.accept_12_4_9_6_1_440 16 93 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 93 162 3 5 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 93 162 (Polychromatic418967fa.accept_11_3_5_8_1_458 14 93 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 93 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 93 162 3 4 31 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 93 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 93 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 93 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 93 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 93 162 3 3 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 93 162 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 93 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 93 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 93 162 3 2 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 93 162 (Polychromatic418967fa.accept_10_5_3_2_1_899 5 93 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 162 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 93 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 93 162 3 1 31 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 93 162
  (Polychromatic418967fa.accept_11_2_5_8_1_470 2 93 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 93 162 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 93 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 93 162))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 71 92 162 (Eq.refl Bool.true) (allA_succ_of_gcd 70 92 162 2 35 46 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 92 162
  (Polychromatic418967fa.accept_12_9_8_6_1_466 69 92 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 92 162 2 34 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 92 162 (accept_3_4 67 92 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 92
  162 2 33 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65
  92 162 (Polychromatic418967fa.accept_15_5_2_12_1_2543 65 92 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 92 162 2 32 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 92 162 (Polychromatic418967fa.accept_12_3_8_6_1_895 63 92 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 92 162 2 31 46 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 92 162 (accept_3_4 61 92 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 92 162 2 30 46 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 92 162
  (Polychromatic418967fa.accept_13_7_1_6_1_3287 59 92 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 92 162 2 29 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 92 162 (Polychromatic418967fa.accept_12_9_8_6_1_466 57 92 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 92 162 2 28 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 92 162 (accept_3_4 55 92 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 92 162 2 27 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 92 162 (Polychromatic418967fa.accept_17_2_7_9_1_2796 53 92 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 92 162 2 26 46 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 92 162
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 51 92 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 92 162 2 25 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 92 162 (accept_3_4 49 92 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 92
  162 2 24 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  92 162 (Polychromatic418967fa.accept_13_8_1_6_1_997 47 92 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 92 162 2 23 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 92 162 (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 92 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 92 162 2 22 46 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 92 162 (accept_3_4 43 92 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 92 162 2 21 46 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 92 162
  (Polychromatic418967fa.accept_13_2_1_6_1_2365 41 92 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 92 162 2 20 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 92 162 (Polychromatic418967fa.accept_12_3_8_6_1_895 39 92 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 92 162 2 19 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 92 162 (accept_3_4 37 92 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 92 162 2 18 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 92 162 (Polychromatic418967fa.accept_13_9_1_6_1_510 35 92 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 92 162 2 17 46 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 92 162
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 92 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 92 162 2 16 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 92 162 (accept_3_4 31 92 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 92
  162 2 15 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  92 162 (Polychromatic418967fa.accept_11_7_4_8_1_1371 29 92 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 92 162 2 14 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 92 162 (Polychromatic418967fa.accept_12_3_8_6_1_895 27 92 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 92 162 2 13 46 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 92 162 (accept_3_4 25 92 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 92 162 2 12 46 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 92 162
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 23 92 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 92 162 2 11 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 92 162 (Polychromatic418967fa.accept_12_9_8_6_1_466 21 92 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 92 162 2 10 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 92 162 (accept_3_4 19 92 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92 162 2 9 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 92 162 (Polychromatic418967fa.accept_16_1_12_2_1_2136 17 92 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 92 162 2 8 46 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 92 162
  (Polychromatic418967fa.accept_12_3_8_6_1_895 15 92 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 92 162 2 7 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 92 162 (accept_3_4 13 92 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92
  162 2 6 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  92 162 (Polychromatic418967fa.accept_31_11_30_7_1_8991 11 92 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 92 162 2 5 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 92 162 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 92 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 92 162 2 4 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 92 162 (accept_3_4 7 92 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 162 2 3 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 92 162 (Polychromatic418967fa.accept_13_5_1_6_1_2367 5 92 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 92 162 2 2 46 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 92 162
  (Polychromatic418967fa.accept_12_3_8_6_1_895 3 92 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 92 162 2 1 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 92 162 (accept_3_4 1 92 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  162))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 91 162 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 91 162 (accept_3_5 71 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  91 162 (Polychromatic418967fa.accept_16_6_11_2_1_6485 70 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 91 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 91 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 91 162 (accept_3_5 68 91 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 91 162 (Polychromatic418967fa.accept_17_16_6_9_1_7769 67 91 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 91 162
  (Polychromatic418967fa.accept_10_6_1_2_1_874 66 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 91 162 (accept_3_5 65 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  91 162 (Polychromatic418967fa.accept_15_4_1_12_1_914 64 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 91 162 (Polychromatic418967fa.accept_10_3_1_2_1_521 63 91 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 91 162 (accept_3_5 62 91 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 91 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 91 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 91 162
  (Polychromatic418967fa.accept_11_5_3_8_1_454 60 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 91 162 (accept_3_5 59 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  91 162 (Polychromatic418967fa.accept_15_13_1_12_1_1638 58 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 91 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 91 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 91 162 (accept_3_5 56 91 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 91 162 (Polychromatic418967fa.accept_14_13_7_8_1_677 55 91 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 91 162
  (Polychromatic418967fa.accept_16_6_11_2_1_6485 54 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 91 162 (accept_3_5 53 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  91 162 (Polychromatic418967fa.accept_19_14_15_10_1_3359 52 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 91 162 (Polychromatic418967fa.accept_21_9_7_15_1_5769 51 91 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 162 (accept_3_5 50 91 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 91 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 91 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 91 162
  (Polychromatic418967fa.accept_14_6_7_8_1_624 48 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 91 162 (accept_3_5 47 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  91 162 (Polychromatic418967fa.accept_10_6_1_2_1_874 46 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 91 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 91 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 162 (accept_3_5 44 91 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 162 (Polychromatic418967fa.accept_10_3_1_2_1_521 43 91 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 91 162
  (Polychromatic418967fa.accept_17_8_6_9_1_7768 42 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 91 162 (accept_3_5 41 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  91 162 (Polychromatic418967fa.accept_21_19_7_15_1_2848 40 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 91 162 (Polychromatic418967fa.accept_10_9_1_2_1_522 39 91 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 162 (accept_3_5 38 91 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 91 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 162
  (Polychromatic418967fa.accept_10_6_1_2_1_874 36 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 91 162 (accept_3_5 35 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  91 162 (Polychromatic418967fa.accept_14_6_7_8_1_624 34 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 91 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 91 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 162 (accept_3_5 32 91 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 162 (Polychromatic418967fa.accept_21_10_7_15_1_8930 31 91 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 162
  (Polychromatic418967fa.accept_19_11_15_10_1_7406 30 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 91 162 (accept_3_5 29 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 91 162 (Polychromatic418967fa.accept_11_6_3_8_1_843 28 91 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 91 162 (Polychromatic418967fa.accept_11_5_3_8_1_454 27 91 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 162 (accept_3_5 26 91 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 25
  91 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 162
  (Polychromatic418967fa.accept_19_5_15_10_1_7405 24 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 162 (accept_3_5 23 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 162 (Polychromatic418967fa.accept_16_6_11_2_1_6485 22 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 91 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 162 (accept_3_5 20 91 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 162 (Polychromatic418967fa.accept_10_9_1_2_1_522 19 91 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 162
  (Polychromatic418967fa.accept_21_18_7_15_1_2877 18 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 91 162 (accept_3_5 17 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  91 162 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 162 (Polychromatic418967fa.accept_14_1_7_8_1_2063 15 91 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 162 (accept_3_5 14 91 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 91 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 162
  (Polychromatic418967fa.accept_21_12_7_15_1_7272 12 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 162 (accept_3_5 11 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 162 (Polychromatic418967fa.accept_21_10_7_15_1_8930 10 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 91 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 162 (accept_3_5 8 91 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 162 (Polychromatic418967fa.accept_16_7_11_2_1_3117 7 91 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 162
  (Polychromatic418967fa.accept_10_6_1_2_1_874 6 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 162 (accept_3_5 5 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  162 (Polychromatic418967fa.accept_15_4_1_12_1_914 4 91 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 91 162 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 91 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 162 (accept_3_5 2 91 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 91 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  162)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 90 162 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 90 162 18 4 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 90 162 (Polychromatic418967fa.accept_11_5_2_8_1_866 71 90 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90 162 2 35 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 90 162 3 23 30 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 90 162 2 34 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 90 162 (Polychromatic418967fa.accept_13_2_12_6_1_2394
  67 90 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 90 162 6 11 15 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 90 162
  (Polychromatic418967fa.accept_7_2_6_1_1_73 65 90 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 90 162 2 32 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 90 162 9 7 10 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 90 162 2 31 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 90 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 90 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90 162 6 10 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 162 (Polychromatic418967fa.accept_13_7_12_6_1_1039
  59 90 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 90 162 2 29 45 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 90 162 3 19 30 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 90 162 2 28 45 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 90 162
  (Polychromatic418967fa.accept_20_15_10_2_1_5924 55 90 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 90 162 18 3 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 90 162 (Polychromatic418967fa.accept_19_15_14_10_1_4667 53 90 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 90 162 2 26 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 90 162 3 17 30 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 90 162 2 25 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 90 162 (Polychromatic418967fa.accept_11_5_2_8_1_866 49
  90 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 162 6 8 15 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 162
  (Polychromatic418967fa.accept_7_5_6_1_1_407 47 90 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 90 162 2 23 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 90 162 9 5 10 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 90 162 2 22 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 90 162 (Polychromatic418967fa.accept_19_5_14_10_1_8933 43 90 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 162 6 7 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 162 (Polychromatic418967fa.accept_13_2_12_6_1_2394 41 90 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 162 2 20 45 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 90 162 3 13 30 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 90 162 2 19 45 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 90 162
  (Polychromatic418967fa.accept_7_2_6_1_1_73 37 90 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 162 18 2 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 90 162 (Polychromatic418967fa.accept_14_7_6_8_1_2856 35 90 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 90 162 2 17 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 90 162 3 11 30 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 90 162 2 16 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 90 162 (Polychromatic418967fa.accept_13_5_12_6_1_508
  31 90 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 162 6 5 15 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 162
  (Polychromatic418967fa.accept_17_12_5_9_1_6372 29 90 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 90 162 2 14 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 90 162 9 3 10 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 90 162 2 13 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 90 162 (Polychromatic418967fa.accept_19_6_14_10_1_4624 25 90 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 162 6 4 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 90 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 162 2 11 45 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 90 162 3 7 30 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 90 162 2 10 45 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 162
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 90 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 162 18 1 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 162 (Polychromatic418967fa.accept_21_17_6_15_1_5765 17 90 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 162 2 8 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 90 162 3 5 30 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 90 162 2 7 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 162 (Polychromatic418967fa.accept_17_13_5_9_1_1762 13 90 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 162 6 2 15 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 162
  (Polychromatic418967fa.accept_21_11_6_15_1_5764 11 90 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 90 162 2 5 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 90 162 9 1 10 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 90 162 2 4 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 90 162 (Polychromatic418967fa.accept_13_7_12_6_1_1039 7 90 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 162 6 1 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 90 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 162 2 2 45 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 90 162 3 1 30 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 90 162 2 1 45 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 162
  (Polychromatic418967fa.accept_19_1_14_10_1_4619 1 90 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 162))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 89 162
  (Eq.refl Bool.true) (allA_succ_of_accept 73 89 162 (accept_3_4 73 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 89 162 (Polychromatic418967fa.accept_20_12_9_2_1_4472 72 89 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 89 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 89 162 (accept_3_4 70 89 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 89 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 69
  89 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 89 162
  (Polychromatic418967fa.accept_25_18_14_12_1_8990 68 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 89 162 (accept_3_4 67 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 89 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 89 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 162 (Polychromatic418967fa.accept_16_1_9_2_1_4161 65 89 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 89 162 (accept_3_4 64 89 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 89 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 63
  89 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 89 162
  (Polychromatic418967fa.accept_7_6_5_1_1_416 62 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 89 162 (accept_3_4 61 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  89 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 89 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 89 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 89 162 (accept_3_4 58 89 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 89 162 (Polychromatic418967fa.accept_10_7_9_2_1_1887 57 89 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 89 162
  (Polychromatic418967fa.accept_13_4_11_6_1_1033 56 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 89 162 (accept_3_4 55 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  89 162 (Polychromatic418967fa.accept_15_9_14_12_1_913 54 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 89 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 89 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 89 162 (accept_3_4 52 89 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 89 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 89 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 89 162
  (Polychromatic418967fa.accept_21_8_5_15_1_4208 50 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 89 162 (accept_3_4 49 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  89 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 89 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 89 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 89 162 (accept_3_4 46 89 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 89 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 89 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 89 162
  (Polychromatic418967fa.accept_13_5_11_6_1_505 44 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 89 162 (accept_3_4 43 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  89 162 (Polychromatic418967fa.accept_19_4_13_10_1_7382 42 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 89 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 89 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 89 162 (accept_3_4 40 89 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 89 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 89 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 89 162
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 89 162 (accept_3_4 37 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  89 162 (Polychromatic418967fa.accept_17_2_4_9_1_2791 36 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 89 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 89 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 89 162 (accept_3_4 34 89 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 89 162 (Polychromatic418967fa.accept_16_1_9_2_1_4161 33 89 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 89 162
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 89 162 (accept_3_4 31 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  89 162 (Polychromatic418967fa.accept_13_4_11_6_1_1033 30 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 89 162 (Polychromatic418967fa.accept_17_12_4_9_1_3889 29 89 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 89 162 (accept_3_4 28 89 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 89 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 89 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 89 162
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 26 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 89 162 (accept_3_4 25 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  89 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 89 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 89 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 89 162 (accept_3_4 22 89 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 89 162 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 89 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 89 162
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 89 162 (accept_3_4 19 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  89 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 89 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 89 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 89 162 (accept_3_4 16 89 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 89 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 89 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 162
  (Polychromatic418967fa.accept_17_14_4_9_1_2792 14 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 89 162 (accept_3_4 13 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  89 162 (Polychromatic418967fa.accept_16_12_9_2_1_8989 12 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 89 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 89 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 89 162 (accept_3_4 10 89 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 89 162 (Polychromatic418967fa.accept_15_9_14_12_1_913 9 89 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 162
  (Polychromatic418967fa.accept_13_8_11_6_1_1035 8 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 89 162 (accept_3_4 7 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89
  162 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 89 162 (Polychromatic418967fa.accept_13_5_11_6_1_505 5 89 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 162 (accept_3_4 4 89 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 89 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 89 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 162 (Polychromatic418967fa.accept_15_2_14_12_1_2453
  2 89 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 162 (accept_3_4 1 89
  162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89
  162)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 88 162 (Eq.refl
  Bool.true) (allA_succ_of_gcd 74 88 162 2 37 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 88 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 73 88 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 88 162 2 36 44 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 88 162 (accept_3_5 71 88 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 88 162 2 35 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 88 162 (Polychromatic418967fa.accept_12_9_4_6_1_460 69
  88 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 88 162 2 34 44 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 88 162
  (Polychromatic418967fa.accept_13_2_10_6_1_1676 67 88 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 88 162 2 33 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 88 162 (accept_3_5 65 88 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 88
  162 2 32 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63
  88 162 (Polychromatic418967fa.accept_12_3_4_6_1_434 63 88 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 88 162 2 31 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 88 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 61 88 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 88 162 2 30 44 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 88 162 (accept_3_5 59 88 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 88 162 2 29 44 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 88 162
  (Polychromatic418967fa.accept_12_9_4_6_1_460 57 88 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 88 162 2 28 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 88 162 (Polychromatic418967fa.accept_10_5_8_2_1_517 55 88 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 88 162 2 27 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 88 162 (accept_3_5 53 88 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 88 162 2 26 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 88 162 (Polychromatic418967fa.accept_12_3_4_6_1_434 51 88 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 88 162 2 25 44 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 88 162
  (Polychromatic418967fa.accept_19_11_12_10_1_7480 49 88 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 88 162 2 24 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 88 162 (accept_3_5 47 88 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 88 162 2 23 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 88 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 88 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 88 162 2 22 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 88 162 (Polychromatic418967fa.accept_13_4_10_6_1_989
  43 88 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 88 162 2 21 44 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 88 162 (accept_3_5 41
  88 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 88 162 2 20 44 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 88 162
  (Polychromatic418967fa.accept_12_3_4_6_1_434 39 88 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 88 162 2 19 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 88 162 (Polychromatic418967fa.accept_38_37_12_10_1_8988 37 88 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 88 162 2 18 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 88 162 (accept_3_5 35 88 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 88 162 2 17 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 88 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 88 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 88 162 2 16 44 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 88 162
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 88 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 88 162 2 15 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 88 162 (accept_3_5 29 88 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 88
  162 2 14 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  88 162 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 88 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 88 162 2 13 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 88 162 (Polychromatic418967fa.accept_10_5_8_2_1_517 25 88 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 88 162 2 12 44 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 88 162 (accept_3_5 23 88 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88 162 2 11 44 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 88 162
  (Polychromatic418967fa.accept_12_9_4_6_1_460 21 88 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 88 162 2 10 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 88 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 88 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 88 162 2 9 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 88 162 (accept_3_5 17 88 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 88 162 2 8 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 88 162 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 88 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 88 162 2 7 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 88 162 (Polychromatic418967fa.accept_28_13_4_22_1_8987
  13 88 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 88 162 2 6 44 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 88 162 (accept_3_5 11
  88 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 88 162 2 5 44 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 88 162
  (Polychromatic418967fa.accept_12_9_4_6_1_460 9 88 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 88 162 2 4 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 88 162 (Polychromatic418967fa.accept_24_7_16_18_1_8986 7 88 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 88 162 2 3 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 88 162 (accept_3_5 5 88 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 88 162 2 2 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 88 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 88 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 88 162 2 1 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 88 162 (Polychromatic418967fa.accept_15_1_13_12_1_347 1
  88 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  162))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 87 162 (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 87 162 3 25 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 87 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 74 87 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 87 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 73
  87 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 87 162 3 24 29 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 87 162
  (Polychromatic418967fa.accept_21_8_3_15_1_2875 71 87 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 87 162 (Polychromatic418967fa.accept_12_10_3_6_1_882 70 87 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 87 162 3 23 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 87 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 68
  87 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 162
  (Polychromatic418967fa.accept_7_4_3_1_1_87 67 87 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 87 162 3 22 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 87 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 87 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 162 (Polychromatic418967fa.accept_10_4_7_2_1_211 64 87 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 87 162 3 21 29 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 87 162
  (Polychromatic418967fa.accept_12_2_3_6_1_112 62 87 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 87 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 87 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 87 162 3 20 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 87 162 (Polychromatic418967fa.accept_10_9_7_2_1_887 59
  87 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 162
  (Polychromatic418967fa.accept_7_2_3_1_1_10 58 87 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 87 162 3 19 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 87 162 (Polychromatic418967fa.accept_12_8_3_6_1_909 56 87 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 162 (Polychromatic418967fa.accept_10_5_7_2_1_516 55 87 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 87 162 3 18 29 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 87 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 87 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 87 162 (Polychromatic418967fa.accept_12_4_3_6_1_879 52 87 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 87 162 3 17 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 87 162 (Polychromatic418967fa.accept_12_2_3_6_1_112 50
  87 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 87 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 87 162 3 16 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 87 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 87 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 87 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 87 162 3 15 29 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 87 162
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 87 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 162 (Polychromatic418967fa.accept_13_4_9_6_1_2376 43 87 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 87 162 3 14 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 87 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 87
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 162
  (Polychromatic418967fa.accept_7_5_3_1_1_424 40 87 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 87 162 3 13 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 87 162 (Polychromatic418967fa.accept_12_2_3_6_1_112 38 87 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 87 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 87 162 3 12 29 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 87 162
  (Polychromatic418967fa.accept_10_5_7_2_1_516 35 87 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 87 162 (Polychromatic418967fa.accept_10_4_7_2_1_211 34 87 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 87 162 3 11 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 87 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 32
  87 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 162
  (Polychromatic418967fa.accept_11_9_10_8_1_444 31 87 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 87 162 3 10 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 87 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 87 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 162 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 87 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 87 162 3 9 29 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 87 162
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 87 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 87 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 87 162 3 8 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 87 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 87 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 162
  (Polychromatic418967fa.accept_12_10_3_6_1_882 22 87 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 87 162 3 7 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 87 162 (Polychromatic418967fa.accept_11_9_10_8_1_444 20 87 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 87 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 162 3 6 29 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 87 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 87 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 87 162 3 5 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 87 162 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 87 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 87 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 87 162 3 4 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 87 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 87 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 162 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 87 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 162 3 3 29 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 162
  (Polychromatic418967fa.accept_12_8_3_6_1_909 8 87 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 162 (Polychromatic418967fa.accept_13_7_9_6_1_148 7 87 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 87 162 3 2 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 87 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 87 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 162
  (Polychromatic418967fa.accept_7_4_3_1_1_87 4 87 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 87 162 3 1 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 87 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 87 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 87 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  162)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 86 162 (Eq.refl
  Bool.true) (allA_succ_of_gcd 76 86 162 2 38 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 86 162 (Polychromatic418967fa.accept_12_3_2_6_1_138 75 86 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 86 162 2 37 43 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 86 162 (accept_3_4 73 86 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 86 162 2 36 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 86 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 71
  86 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 86 162 2 35 43 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 86 162
  (Polychromatic418967fa.accept_7_6_2_1_1_214 69 86 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 86 162 2 34 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 86 162 (accept_3_4 67 86 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 86
  162 2 33 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65
  86 162 (Polychromatic418967fa.accept_11_10_9_8_1_1974 65 86 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 86 162 2 32 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 86 162 (Polychromatic418967fa.accept_12_3_2_6_1_138 63 86 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 86 162 2 31 43 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 86 162 (accept_3_4 61 86 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 86 162 2 30 43 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 86 162
  (Polychromatic418967fa.accept_7_3_2_1_1_225 59 86 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 86 162 2 29 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 86 162 (Polychromatic418967fa.accept_12_9_2_6_1_455 57 86 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 86 162 2 28 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 86 162 (accept_3_4 55 86 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 86 162 2 27 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 86 162 (Polychromatic418967fa.accept_13_1_8_6_1_1016 53 86 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 86 162 2 26 43 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 86 162
  (Polychromatic418967fa.accept_10_1_6_2_1_867 51 86 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 86 162 2 25 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 86 162 (accept_3_4 49 86 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 86
  162 2 24 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  86 162 (Polychromatic418967fa.accept_22_3_20_8_1_8985 47 86 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 86 162 2 23 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 86 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 86 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 86 162 2 22 43 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 86 162 (accept_3_4 43 86 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 86 162 2 21 43 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 86 162
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 86 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 86 162 2 20 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 86 162 (Polychromatic418967fa.accept_12_3_2_6_1_138 39 86 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 86 162 2 19 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 86 162 (accept_3_4 37 86 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 86 162 2 18 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 86 162 (Polychromatic418967fa.accept_16_3_6_2_1_4157 35 86 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 86 162 2 17 43 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 86 162
  (Polychromatic418967fa.accept_12_9_2_6_1_455 33 86 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 86 162 2 16 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 86 162 (accept_3_4 31 86 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 86
  162 2 15 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  86 162 (Polychromatic418967fa.accept_14_1_2_8_1_655 29 86 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 86 162 2 14 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 86 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 86 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 86 162 2 13 43 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 86 162 (accept_3_4 25 86 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 86 162 2 12 43 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 86 162
  (Polychromatic418967fa.accept_15_8_11_12_1_1626 23 86 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 86 162 2 11 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 86 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 86 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 86 162 2 10 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 86 162 (accept_3_4 19 86 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 86 162 2 9 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 86 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 86 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 162 2 8 43 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 162
  (Polychromatic418967fa.accept_12_3_2_6_1_138 15 86 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 86 162 2 7 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 86 162 (accept_3_4 13 86 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86
  162 2 6 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  86 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 86 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 86 162 2 5 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 86 162 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 86 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 162 2 4 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 162 (accept_3_4 7 86 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 86 162 2 3 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 86 162 (Polychromatic418967fa.accept_29_5_28_17_1_8984 5 86 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 162 2 2 43 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 162
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 86 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 86 162 2 1 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 86 162 (accept_3_4 1 86 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  162))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 85 162 (Eq.refl
  Bool.true) (allA_succ_of_accept 77 85 162 (accept_3_5 77 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 85 162 (Polychromatic418967fa.accept_22_10_19_8_1_8983 76 85 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 85 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 85 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 162 (accept_3_5 74 85 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 162 (Polychromatic418967fa.accept_10_3_5_2_1_38 73
  85 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 162
  (Polychromatic418967fa.accept_14_2_1_8_1_650 72 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 162 (accept_3_5 71 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  85 162 (Polychromatic418967fa.accept_19_13_9_10_1_2181 70 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 85 162 (Polychromatic418967fa.accept_13_4_7_6_1_2359 69 85 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 162 (accept_3_5 68 85 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 85 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 162
  (Polychromatic418967fa.accept_13_1_7_6_1_142 66 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 85 162 (accept_3_5 65 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  85 162 (Polychromatic418967fa.accept_13_12_7_6_1_1015 64 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 85 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 85 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 162 (accept_3_5 62 85 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 162 (Polychromatic418967fa.accept_13_9_7_6_1_1673 61 85 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 85 162
  (Polychromatic418967fa.accept_19_3_9_10_1_8982 60 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 85 162 (accept_3_5 59 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  85 162 (Polychromatic418967fa.accept_10_8_5_2_1_881 58 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 85 162 (Polychromatic418967fa.accept_10_7_5_2_1_880 57 85 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 162 (accept_3_5 56 85 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 85 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 85 162
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 54 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 85 162 (accept_3_5 53 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  85 162 (Polychromatic418967fa.accept_15_7_10_12_1_2403 52 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 85 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 85 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 162 (accept_3_5 50 85 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 162 (Polychromatic418967fa.accept_14_7_1_8_1_2873 49 85 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 162
  (Polychromatic418967fa.accept_10_8_5_2_1_881 48 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 85 162 (accept_3_5 47 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  85 162 (Polychromatic418967fa.accept_25_21_10_12_1_8981 46 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 85 162 (Polychromatic418967fa.accept_16_13_5_2_1_2131 45 85 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 162 (accept_3_5 44 85 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 85 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 162
  (Polychromatic418967fa.accept_19_4_9_10_1_8928 42 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 162 (accept_3_5 41 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 162 (Polychromatic418967fa.accept_13_1_7_6_1_142 40 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 85 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 162 (accept_3_5 38 85 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 162 (Polychromatic418967fa.accept_10_7_5_2_1_880 37 85 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 162
  (Polychromatic418967fa.accept_15_6_10_12_1_2538 36 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 162 (accept_3_5 35 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 162 (Polychromatic418967fa.accept_19_15_9_10_1_4615 34 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 162 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 85 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 162 (accept_3_5 32 85 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 85 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 162
  (Polychromatic418967fa.accept_13_4_7_6_1_2359 30 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 162 (accept_3_5 29 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 162 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 85 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 162 (accept_3_5 26 85 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 162 (Polychromatic418967fa.accept_13_12_7_6_1_1015 25 85 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 162
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 24 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 162 (accept_3_5 23 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 162 (Polychromatic418967fa.accept_13_9_7_6_1_1673 22 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 162 (Polychromatic418967fa.accept_14_7_1_8_1_2873 21 85 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 162 (accept_3_5 20 85 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 85 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 162
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 162 (accept_3_5 17 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 162 (Polychromatic418967fa.accept_14_2_1_8_1_650 16 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 85 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 162 (accept_3_5 14 85 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 162 (Polychromatic418967fa.accept_10_3_5_2_1_38 13 85 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 162
  (Polychromatic418967fa.accept_13_12_7_6_1_1015 12 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 162 (accept_3_5 11 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 162 (Polychromatic418967fa.accept_20_10_5_2_1_3102 10 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 162 (Polychromatic418967fa.accept_13_9_7_6_1_1673 9 85 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 162 (accept_3_5 8 85 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 85 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 162
  (Polychromatic418967fa.accept_15_6_10_12_1_2538 6 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 162 (accept_3_5 5 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  162 (Polychromatic418967fa.accept_13_4_7_6_1_2359 4 85 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 85 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 85 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 162 (accept_3_5 2 85 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 162 (Polychromatic418967fa.accept_13_1_7_6_1_142 1 85 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  162)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 84 162 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 84 162 6 13 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 84 162 (Polychromatic418967fa.accept_10_7_4_2_1_903 77 84 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 84 162 2 38 42 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 84 162 3 25 28 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 84 162 2 37 42 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 84 162
  (Polychromatic418967fa.accept_19_16_8_10_1_7431 73 84 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 84 162 6 12 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 84 162 (Polychromatic418967fa.accept_24_23_12_18_1_8980 71 84 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 162 2 35 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 84 162 3 23 28 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 84 162 2 34 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 84 162 (Polychromatic418967fa.accept_10_7_4_2_1_903 67
  84 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 84 162 6 11 14 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 84 162
  (Polychromatic418967fa.accept_15_5_9_12_1_1599 65 84 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 84 162 2 32 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 84 162 3 21 28 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 84 162 2 31 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 84 162 (Polychromatic418967fa.accept_17_10_16_9_1_5127 61 84 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 162 6 10 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 162 (Polychromatic418967fa.accept_11_4_7_8_1_1926
  59 84 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 84 162 2 29 42 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 84 162 3 19 28 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 84 162 2 28 42 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 84 162
  (Polychromatic418967fa.accept_15_10_9_12_1_2497 55 84 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 84 162 6 9 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 84 162 (Polychromatic418967fa.accept_22_9_18_8_1_8979 53 84 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 84 162 2 26 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 84 162 3 17 28 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 84 162 2 25 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 84 162 (Polychromatic418967fa.accept_15_4_9_12_1_2495
  49 84 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84 162 6 8 14 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 162
  (Polychromatic418967fa.accept_10_7_4_2_1_903 47 84 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 84 162 2 23 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 84 162 3 15 28 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 84 162 2 22 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 84 162 (Polychromatic418967fa.accept_19_5_8_10_1_8978 43 84 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 162 6 7 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 162 (Polychromatic418967fa.accept_22_19_18_8_1_8915 41 84
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84 162 2 20 42 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 84 162 3 13 28 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 84 162 2 19 42 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 84 162
  (Polychromatic418967fa.accept_10_7_4_2_1_903 37 84 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 84 162 6 6 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 84 162 (Polychromatic418967fa.accept_15_5_9_12_1_1599 35 84 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84 162 2 17 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 84 162 3 11 28 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 84 162 2 16 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 162 (Polychromatic418967fa.accept_19_12_8_10_1_8948
  31 84 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 162 6 5 14 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 162
  (Polychromatic418967fa.accept_15_14_9_12_1_2498 29 84 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 84 162 2 14 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 84 162 3 9 28 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 84 162 2 13 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 84 162 (Polychromatic418967fa.accept_15_10_9_12_1_2497 25 84 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 162 6 4 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 162 (Polychromatic418967fa.accept_17_6_16_9_1_5129 23 84 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 162 2 11 42 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 84 162 3 7 28 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 84 162 2 10 42 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 84 162
  (Polychromatic418967fa.accept_15_4_9_12_1_2495 19 84 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 84 162 6 3 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 84 162 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 84 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84 162 2 8 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 84 162 3 5 28 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 84 162 2 7 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 162 (Polychromatic418967fa.accept_17_13_16_9_1_5128 13 84
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 162 6 2 14 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 162
  (Polychromatic418967fa.accept_19_11_8_10_1_8901 11 84 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 84 162 2 5 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 84 162 3 3 28 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 84 162 2 4 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 84 162 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 84 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 162 6 1 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 162 (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 84 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 162 2 2 42 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 84 162 3 1 28 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 84 162 2 1 42 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 162
  (Polychromatic418967fa.accept_22_1_18_8_1_5619 1 84 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 84 162))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 83 162
  (Eq.refl Bool.true) (allA_succ_of_accept 79 83 162 (accept_3_4 79 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 83 162 (Polychromatic418967fa.accept_15_3_8_12_1_900 78 83 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 83 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 83 162 (accept_3_4 76 83 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 83 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 75
  83 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 83 162
  (Polychromatic418967fa.accept_17_6_15_9_1_1791 74 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 83 162 (accept_3_4 73 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  83 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 83 162 (Polychromatic418967fa.accept_10_1_3_2_1_220 71 83 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 83 162 (accept_3_4 70 83 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 83 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 83 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 83 162
  (Polychromatic418967fa.accept_7_5_6_1_1_407 68 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 83 162 (accept_3_4 67 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  83 162 (Polychromatic418967fa.accept_13_1_5_6_1_1048 66 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 83 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 83 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 83 162 (accept_3_4 64 83 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 83 162 (Polychromatic418967fa.accept_13_11_5_6_1_519 63 83 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 83 162
  (Polychromatic418967fa.accept_13_10_5_6_1_1671 62 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 83 162 (accept_3_4 61 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  83 162 (Polychromatic418967fa.accept_19_3_7_10_1_6023 60 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 83 162 (Polychromatic418967fa.accept_20_19_3_2_1_3118 59 83 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 83 162 (accept_3_4 58 83 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 83 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 83 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 83 162
  (Polychromatic418967fa.accept_13_4_5_6_1_3201 56 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 83 162 (accept_3_4 55 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  83 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 83 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 83 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 83 162 (accept_3_4 52 83 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 83 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 83 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 83 162
  (Polychromatic418967fa.accept_13_11_5_6_1_519 50 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 83 162 (accept_3_4 49 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  83 162 (Polychromatic418967fa.accept_15_3_8_12_1_900 48 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 83 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 83 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 83 162 (accept_3_4 46 83 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 83 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 83 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 83 162
  (Polychromatic418967fa.accept_7_2_6_1_1_73 44 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 83 162 (accept_3_4 43 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  83 162 (Polychromatic418967fa.accept_13_3_5_6_1_3192 42 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 83 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 83 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 83 162 (accept_3_4 40 83 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 83 162 (Polychromatic418967fa.accept_19_1_7_10_1_8926 39 83 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 83 162
  (Polychromatic418967fa.accept_13_12_5_6_1_1050 38 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 83 162 (accept_3_4 37 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  83 162 (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 83 162 (Polychromatic418967fa.accept_10_5_3_2_1_899 35 83 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 83 162 (accept_3_4 34 83 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 83 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 83 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 83 162
  (Polychromatic418967fa.accept_23_9_14_1_1_8977 32 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 83 162 (accept_3_4 31 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  83 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 83 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 83 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 83 162 (accept_3_4 28 83 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 83 162 (Polychromatic418967fa.accept_13_1_5_6_1_1048 27 83 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 83 162
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 83 162 (accept_3_4 25 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  83 162 (Polychromatic418967fa.accept_13_11_5_6_1_519 24 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 83 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 83 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 83 162 (accept_3_4 22 83 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 83 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 83 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 83 162
  (Polychromatic418967fa.accept_15_5_8_12_1_2435 20 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 83 162 (accept_3_4 19 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  83 162 (Polychromatic418967fa.accept_15_3_8_12_1_900 18 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 83 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 83 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 83 162 (accept_3_4 16 83 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 83 162 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 83 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 83 162
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 14 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 83 162 (accept_3_4 13 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  83 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 83 162 (Polychromatic418967fa.accept_10_1_3_2_1_220 11 83 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 83 162 (accept_3_4 10 83 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 83 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 83 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 83 162
  (Polychromatic418967fa.accept_24_8_11_18_1_8976 8 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 83 162 (accept_3_4 7 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 83
  162 (Polychromatic418967fa.accept_16_6_3_2_1_3096 6 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 83 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 83 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 162 (accept_3_4 4 83 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 83 162 (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 83 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 162
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 83 162 (accept_3_4 1 83 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83
  162)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 82 162 (Eq.refl
  Bool.true) (allA_succ_of_gcd 80 82 162 2 40 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 82 162 (Polychromatic418967fa.accept_11_2_5_8_1_470 79 82 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 82 162 2 39 41 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 82 162 (accept_3_5 77 82 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 82 162 2 38 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 82 162 (Polychromatic418967fa.accept_12_3_10_6_1_442
  75 82 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 82 162 2 37 41 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 82 162
  (Polychromatic418967fa.accept_7_3_5_1_1_72 73 82 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 82 162 2 36 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 82 162 (accept_3_5 71 82 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 82
  162 2 35 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  82 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 82 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 82 162 2 34 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 82 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 67 82 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 82 162 2 33 41 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 82 162 (accept_3_5 65 82 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 82 162 2 32 41 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 82 162
  (Polychromatic418967fa.accept_12_3_10_6_1_442 63 82 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 82 162 2 31 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 82 162 (Polychromatic418967fa.accept_13_9_4_6_1_1005 61 82 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 82 162 2 30 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 82 162 (accept_3_5 59 82 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 82 162 2 29 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 82 162 (Polychromatic418967fa.accept_11_2_5_8_1_470 57 82 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 82 162 2 28 41 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 82 162
  (Polychromatic418967fa.accept_7_6_5_1_1_416 55 82 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 82 162 2 27 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 82 162 (accept_3_5 53 82 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 82
  162 2 26 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  82 162 (Polychromatic418967fa.accept_12_3_10_6_1_442 51 82 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 82 162 2 25 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 82 162 (Polychromatic418967fa.accept_13_10_4_6_1_3224 49 82 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 82 162 2 24 41 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 82 162 (accept_3_5 47 82 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 82 162 2 23 41 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 82 162
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 82 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 82 162 2 22 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 82 162 (Polychromatic418967fa.accept_21_1_19_15_1_8914 43 82 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 82 162 2 21 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 82 162 (accept_3_5 41 82 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 82 162 2 20 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 82 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 82 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 82 162 2 19 41 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 82 162
  (Polychromatic418967fa.accept_13_11_4_6_1_1006 37 82 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 82 162 2 18 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 82 162 (accept_3_5 35 82 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 82
  162 2 17 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  82 162 (Polychromatic418967fa.accept_12_9_10_6_1_872 33 82 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 82 162 2 16 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 82 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 82 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 82 162 2 15 41 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 82 162 (accept_3_5 29 82 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 82 162 2 14 41 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 82 162
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 82 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 82 162 2 13 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 82 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 82 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 82 162 2 12 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 82 162 (accept_3_5 23 82 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 82 162 2 11 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 82 162 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 82 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 82 162 2 10 41 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 82 162
  (Polychromatic418967fa.accept_15_4_7_12_1_5538 19 82 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 82 162 2 9 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 82 162 (accept_3_5 17 82 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 82
  162 2 8 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  82 162 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 82 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 82 162 2 7 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 82 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 82 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 82 162 2 6 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 82 162 (accept_3_5 11 82 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82 162 2 5 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 82 162 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 82 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 82 162 2 4 41 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 82 162
  (Polychromatic418967fa.accept_13_7_4_6_1_3221 7 82 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 82 162 2 3 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 82 162 (accept_3_5 5 82 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 82 162
  2 2 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 82
  162 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 82 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 82 162 2 1 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 82 162 (Polychromatic418967fa.accept_19_1_6_10_1_3366 1 82 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 82
  162))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 162
  (allA_succ_of_accept 80 81 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 80 81 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 81 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 81 162 3 26 27 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 81 162
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 77 81 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 81 162 (Polychromatic418967fa.accept_10_6_1_2_1_874 76 81 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 81 162 3 25 27 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 81 162 (Polychromatic418967fa.accept_12_2_9_6_1_439 74
  81 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 162
  (Polychromatic418967fa.accept_7_3_4_1_1_71 73 81 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 81 162 9 8 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 81 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 81 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 162 (Polychromatic418967fa.accept_12_10_9_6_1_1445 70 81
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 81 162 3 23 27 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 81 162
  (Polychromatic418967fa.accept_7_5_4_1_1_412 68 81 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 81 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 81 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 81 162 3 22 27 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 81 162 (Polychromatic418967fa.accept_15_5_6_12_1_916
  65 81 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 162
  (Polychromatic418967fa.accept_12_4_9_6_1_440 64 81 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 81 162 9 7 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 81 162 (Polychromatic418967fa.accept_11_7_4_8_1_1371 62 81 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 61 81 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 81 162 3 20 27 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 81 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 81 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 162 (Polychromatic418967fa.accept_12_10_9_6_1_1445 58 81 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 81 162 3 19 27 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 81 162 (Polychromatic418967fa.accept_10_6_1_2_1_874 56
  81 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 55 81 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 81 162 27 2 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 81 162 (Polychromatic418967fa.accept_10_3_1_2_1_521 53 81 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 81 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 81 162 3 17 27 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 81 162
  (Polychromatic418967fa.accept_12_2_9_6_1_439 50 81 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 162 (Polychromatic418967fa.accept_10_9_1_2_1_522 49 81 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 81 162 3 16 27 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 81 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  81 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 162
  (Polychromatic418967fa.accept_10_6_1_2_1_874 46 81 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 81 162 9 5 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 81 162 (Polychromatic418967fa.accept_12_8_9_6_1_127 44 81 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 81 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 81 162 3 14 27 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 81 162
  (Polychromatic418967fa.accept_16_9_1_2_1_2126 41 81 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 81 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 81 162 3 13 27 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 81 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 38
  81 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 162
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 37 81 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 81 162 9 4 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 81 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 81 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 162 (Polychromatic418967fa.accept_11_1_4_8_1_1918 34 81 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 81 162 3 11 27 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 81 162
  (Polychromatic418967fa.accept_12_8_9_6_1_127 32 81 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 81 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 81 162 3 10 27 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 81 162 (Polychromatic418967fa.accept_10_9_1_2_1_522 29
  81 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 162
  (Polychromatic418967fa.accept_12_4_9_6_1_440 28 81 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 81 162 27 1 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 81 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 81 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 162 (Polychromatic418967fa.accept_15_10_6_12_1_1645 25 81
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 81 162 3 8 27 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 81 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 81 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 162 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 81 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 81 162 3 7 27 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 81 162 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 81 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 81 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 81 162 9 2 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 81 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 81 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 162 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 81 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 81 162 3 5 27 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 81 162
  (Polychromatic418967fa.accept_12_2_9_6_1_439 14 81 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 162 (Polychromatic418967fa.accept_10_3_1_2_1_521 13 81 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 162 3 4 27 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 81 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 162
  (Polychromatic418967fa.accept_7_3_4_1_1_71 10 81 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 81 162 9 1 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 81 162 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 81 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 81 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 81 162 3 2 27 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 81 162
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 81 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 162 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 81 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 162 3 1 27 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 162 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 81 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 162
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 1 81 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 162))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 162
  (allA_succ_of_accept 79 80 162 (accept_3_4 79 80 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 80
  162 2 39 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77
  80 162 (Polychromatic418967fa.accept_13_12_2_6_1_2396 77 80 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 80 162 2 38 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 80 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 75 80 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 80 162 2 37 40 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 80 162 (accept_3_4 73 80 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 80 162 2 36 40 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 80 162
  (Polychromatic418967fa.accept_11_5_3_8_1_454 71 80 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 80 162 2 35 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 80 162 (Polychromatic418967fa.accept_12_9_8_6_1_466 69 80 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 80 162 2 34 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 80 162 (accept_3_4 67 80 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 80 162 2 33 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 80 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 65 80 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 80 162 2 32 40 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 80 162
  (Polychromatic418967fa.accept_12_3_8_6_1_895 63 80 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 80 162 2 31 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 80 162 (accept_3_4 61 80 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 80
  162 2 30 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  80 162 (Polychromatic418967fa.accept_23_13_11_1_1_7158 59 80 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 80 162 2 29 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 80 162 (Polychromatic418967fa.accept_12_9_8_6_1_466 57 80 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 80 162 2 28 40 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 80 162 (accept_3_4 55 80 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 80 162 2 27 40 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 80 162
  (Polychromatic418967fa.accept_7_4_3_1_1_87 53 80 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 80 162 2 26 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 80 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 80 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 162 2 25 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 162 (accept_3_4 49 80 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 80 162 2 24 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 80 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 80 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 80 162 2 23 40 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 80 162
  (Polychromatic418967fa.accept_12_9_8_6_1_466 45 80 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 80 162 2 22 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 80 162 (accept_3_4 43 80 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 80
  162 2 21 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  80 162 (Polychromatic418967fa.accept_43_41_37_33_1_8975 41 80 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 80 162 2 20 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 80 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 80 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 80 162 2 19 40 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 80 162 (accept_3_4 37 80 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 80 162 2 18 40 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 80 162
  (Polychromatic418967fa.accept_13_9_2_6_1_514 35 80 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 80 162 2 17 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 80 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 80 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 80 162 2 16 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 80 162 (accept_3_4 31 80 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80 162 2 15 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 80 162 (Polychromatic418967fa.accept_21_8_17_15_1_2834 29 80
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 80 162 2 14 40 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 80 162
  (Polychromatic418967fa.accept_11_5_3_8_1_454 27 80 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 80 162 2 13 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 80 162 (accept_3_4 25 80 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 80
  162 2 12 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  80 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 80 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 80 162 2 11 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 80 162 (Polychromatic418967fa.accept_12_9_8_6_1_466 21 80 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 80 162 2 10 40 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 80 162 (accept_3_4 19 80 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80 162 2 9 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 80 162 (Polychromatic418967fa.accept_11_6_3_8_1_843 17
  80 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 80 162 2 8 40 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 80 162
  (Polychromatic418967fa.accept_12_3_8_6_1_895 15 80 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 80 162 2 7 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 80 162 (accept_3_4 13 80 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80
  162 2 6 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  80 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 80 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 80 162 2 5 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 80 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 80 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 80 162 2 4 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 80 162 (accept_3_4 7 80 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 162 2 3 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 80 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 80 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 80 162 2 2 40 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 80 162
  (Polychromatic418967fa.accept_12_3_8_6_1_895 3 80 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 80 162 2 1 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 80 162 (accept_3_4 1 80 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  162)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 162
  (allA_succ_of_accept 78 79 162 (Polychromatic418967fa.accept_23_9_10_1_1_8974 78 79 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 79 162 (accept_3_5 77 79 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 79 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 76 79 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 79 162
  (Polychromatic418967fa.accept_30_15_19_12_1_8973 75 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 79 162 (accept_3_5 74 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 79 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 79 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 79 162 (Polychromatic418967fa.accept_13_7_1_6_1_3287 72 79 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 79 162 (accept_3_5 71 79 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 79 162 (Polychromatic418967fa.accept_13_5_1_6_1_2367
  70 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 79 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 79 162 (accept_3_5 68 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  79 162 (Polychromatic418967fa.accept_10_7_9_2_1_1887 67 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 79 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 79 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 79 162 (accept_3_5 65 79 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 79 162 (Polychromatic418967fa.accept_19_7_3_10_1_4674 64 79 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 79 162
  (Polychromatic418967fa.accept_20_3_19_2_1_5926 63 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 79 162 (accept_3_5 62 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  79 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 79 162 (Polychromatic418967fa.accept_11_5_2_8_1_866 60 79 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 79 162 (accept_3_5 59 79 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 79 162 (Polychromatic418967fa.accept_19_1_3_10_1_8917 58 79 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 79 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 79 162 (accept_3_5 56 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  79 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 79 162 (Polychromatic418967fa.accept_13_2_1_6_1_2365 54 79 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 79 162 (accept_3_5 53 79 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 79 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 79 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 79 162
  (Polychromatic418967fa.accept_10_1_9_2_1_45 51 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 79 162 (accept_3_5 50 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  79 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 79 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 79 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 79 162 (accept_3_5 47 79 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 79 162 (Polychromatic418967fa.accept_13_7_1_6_1_3287 46 79 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 79 162 (accept_3_5 44 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  79 162 (Polychromatic418967fa.accept_14_1_9_8_1_2863 43 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 79 162 (Polychromatic418967fa.accept_13_3_1_6_1_509 42 79 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 162 (accept_3_5 41 79 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 79 162 (Polychromatic418967fa.accept_24_16_7_18_1_8972 40 79 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 162
  (Polychromatic418967fa.accept_15_9_4_12_1_1611 39 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 79 162 (accept_3_5 38 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  79 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 79 162 (Polychromatic418967fa.accept_17_2_11_9_1_1739 36 79 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 162 (accept_3_5 35 79 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 79 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 79 162 (accept_3_5 32 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  79 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 79 162 (Polychromatic418967fa.accept_19_11_3_10_1_3354 30 79 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 162 (accept_3_5 29 79 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 162 (Polychromatic418967fa.accept_13_2_1_6_1_2365 28 79 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 162
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 162 (accept_3_5 26 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 79 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 162 (accept_3_5 23 79 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 162 (Polychromatic418967fa.accept_13_9_1_6_1_510 22 79 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 162 (accept_3_5 20 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 162 (Polychromatic418967fa.accept_16_3_15_2_1_6475 19 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 162 (Polychromatic418967fa.accept_13_5_1_6_1_2367 18 79 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 162 (accept_3_5 17 79 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 162 (Polychromatic418967fa.accept_11_5_2_8_1_866 16 79 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 162
  (Polychromatic418967fa.accept_13_2_1_6_1_2365 15 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 162 (accept_3_5 14 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 162 (Polychromatic418967fa.accept_16_12_15_2_1_6473 12 79 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 162 (accept_3_5 11 79 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 79 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 162 (accept_3_5 8 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  162 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 79 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 79 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 162 (accept_3_5 5 79 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 162 (Polychromatic418967fa.accept_20_4_19_2_1_8971 4 79 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 162
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 162 (accept_3_5 2 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79
  162 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 79 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 79 162))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 162
  (allA_succ_of_accept 77 78 162 (Polychromatic418967fa.accept_15_2_3_12_1_891 77 78 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 78 162 2 38 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 78 162 3 25 26 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 78 162 2 37 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 78 162 (Polychromatic418967fa.accept_15_13_3_12_1_1609
  73 78 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 162 6 12 13 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 162
  (Polychromatic418967fa.accept_17_3_10_9_1_8970 71 78 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 78 162 2 35 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 69 78 162 3 23 26 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 78 162 2 34 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 78 162 (Polychromatic418967fa.accept_15_7_3_12_1_365 67 78 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 162 6 11 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 162 (Polychromatic418967fa.accept_10_5_8_2_1_517 65
  78 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 162 2 32 39 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 78 162 3 21 26 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 78 162 2 31 39 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 78 162
  (Polychromatic418967fa.accept_23_15_9_1_1_8969 61 78 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 162 6 10 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 78 162 (Polychromatic418967fa.accept_11_4_1_8_1_1366 59 78 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78 162 2 29 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 78 162 3 19 26 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 78 162 2 28 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 78 162 (Polychromatic418967fa.accept_10_5_8_2_1_517 55
  78 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 162 6 9 13 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 162
  (Polychromatic418967fa.accept_15_8_3_12_1_1657 53 78 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 78 162 2 26 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 51 78 162 3 17 26 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 78 162 2 25 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 78 162 (Polychromatic418967fa.accept_19_11_2_10_1_8965 49 78 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 162 6 8 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 162 (Polychromatic418967fa.accept_15_2_3_12_1_891 47 78 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 162 2 23 39 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 78 162 3 15 26 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 78 162 2 22 39 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 78 162
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 43 78 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 162 6 7 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 78 162 (Polychromatic418967fa.accept_23_18_9_1_1_8968 41 78 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78 162 2 20 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 78 162 3 13 26 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 78 162 2 19 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 162 (Polychromatic418967fa.accept_11_4_1_8_1_1366
  37 78 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 162 6 6 13 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 162
  (Polychromatic418967fa.accept_10_5_8_2_1_517 35 78 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 78 162 2 17 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 78 162 3 11 26 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 78 162 2 16 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 78 162 (Polychromatic418967fa.accept_19_12_2_10_1_8967 31 78 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 162 6 5 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 162 (Polychromatic418967fa.accept_22_7_12_8_1_4002 29 78 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 162 2 14 39 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 78 162 3 9 26 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 78 162 2 13 39 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 162
  (Polychromatic418967fa.accept_10_5_8_2_1_517 25 78 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 162 6 4 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 78 162 (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 78 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 162 2 11 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 78 162 3 7 26 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 78 162 2 10 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 162 (Polychromatic418967fa.accept_24_19_6_18_1_8966
  19 78 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 162 6 3 13 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 162
  (Polychromatic418967fa.accept_15_2_3_12_1_891 17 78 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 78 162 2 8 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 78 162 3 5 26 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 78 162 2 7 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 78 162 (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 78 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 162 6 2 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 162 (Polychromatic418967fa.accept_19_11_2_10_1_8965 11 78
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78 162 2 5 39 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 78 162 3 3 26 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 78 162 2 4 39 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 162
  (Polychromatic418967fa.accept_15_7_3_12_1_365 7 78 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 78 162 6 1 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 78 162 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 78 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 162 2 2 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 78 162 3 1 26 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 78 162 2 1 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 162 (Polychromatic418967fa.accept_17_1_10_9_1_3884 1 78 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  162)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 162
  (allA_succ_of_accept 76 77 162 (accept_3_4 76 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 162 (Polychromatic418967fa.accept_10_4_7_2_1_211 74 77 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 162 (accept_3_4 73 77 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 162 (Polychromatic418967fa.accept_13_7_12_6_1_1039 72 77 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 162 (accept_3_4 70 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 162 (Polychromatic418967fa.accept_10_9_7_2_1_887 69 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 162 (Polychromatic418967fa.accept_19_11_1_10_1_8962 68 77 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 162 (accept_3_4 67 77 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 162 (Polychromatic418967fa.accept_15_6_2_12_1_885 66 77 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 162
  (Polychromatic418967fa.accept_10_5_7_2_1_516 65 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 162 (accept_3_4 64 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 162 (Polychromatic418967fa.accept_13_10_12_6_1_991 62 77 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 162 (accept_3_4 61 77 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 162 (Polychromatic418967fa.accept_19_3_1_10_1_2193 60 77
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 162 (accept_3_4 58 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 162 (Polychromatic418967fa.accept_13_5_12_6_1_508 57 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 162 (Polychromatic418967fa.accept_22_12_11_8_1_8964 56 77 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 162 (accept_3_4 55 77 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 162 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 77 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 162
  (Polychromatic418967fa.accept_16_5_13_2_1_2138 53 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 162 (accept_3_4 52 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 162 (Polychromatic418967fa.accept_15_5_2_12_1_2543 50 77 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 162 (accept_3_4 49 77 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 162 (Polychromatic418967fa.accept_14_6_7_8_1_624 48 77 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 162 (accept_3_4 46 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 162 (Polychromatic418967fa.accept_10_5_7_2_1_516 45 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 162 (Polychromatic418967fa.accept_10_4_7_2_1_211 44 77 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 162 (accept_3_4 43 77 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 162 (Polychromatic418967fa.accept_19_4_1_10_1_7447 42 77 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 162
  (Polychromatic418967fa.accept_13_2_12_6_1_2394 41 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 162 (accept_3_4 40 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 162 (Polychromatic418967fa.accept_20_18_17_2_1_5941 38 77 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 162 (accept_3_4 37 77 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 162 (Polychromatic418967fa.accept_13_10_12_6_1_991 36 77
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 162 (accept_3_4 34 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 162 (Polychromatic418967fa.accept_13_7_12_6_1_1039 33 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 162 (Polychromatic418967fa.accept_19_13_1_10_1_8963 32 77 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 162 (accept_3_4 31 77 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 162 (Polychromatic418967fa.accept_19_11_1_10_1_8962 30 77
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 162
  (Polychromatic418967fa.accept_10_9_7_2_1_887 29 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 162 (accept_3_4 28 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 162 (Polychromatic418967fa.accept_19_7_1_10_1_4702 26 77 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 162 (accept_3_4 25 77 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 162 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 77 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 162 (accept_3_4 22 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 162 (Polychromatic418967fa.accept_15_6_2_12_1_885 21 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 162 (Polychromatic418967fa.accept_13_7_12_6_1_1039 20 77 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 162 (accept_3_4 19 77 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 162 (Polychromatic418967fa.accept_13_5_12_6_1_508 18 77 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 162
  (Polychromatic418967fa.accept_19_17_1_10_1_4671 17 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 162 (accept_3_4 16 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 162 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 77 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 162 (accept_3_4 13 77 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 162 (Polychromatic418967fa.accept_20_12_17_2_1_8961 12 77 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 162 (accept_3_4 10 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 162 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 162 (Polychromatic418967fa.accept_21_8_14_15_1_5777 8 77 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 162 (accept_3_4 7 77 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 162 (Polychromatic418967fa.accept_14_6_7_8_1_624 6 77 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 162
  (Polychromatic418967fa.accept_10_5_7_2_1_516 5 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 162 (accept_3_4 4 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  162 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 77 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 162 (Polychromatic418967fa.accept_13_2_12_6_1_2394 2 77 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 162 (accept_3_4 1 77 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 162))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 162 (allA_succ_of_accept 75 76 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 75 76 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 76 162 2 37 38 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 76 162
  (Polychromatic418967fa.accept_13_8_11_6_1_1035 73 76 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 76 162 2 36 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 76 162 (accept_3_5 71 76 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 76
  162 2 35 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  76 162 (Polychromatic418967fa.accept_12_9_4_6_1_460 69 76 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 76 162 2 34 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 76 162 (Polychromatic418967fa.accept_17_16_8_9_1_1772 67 76 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 76 162 2 33 38 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 76 162 (accept_3_5 65 76 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 76 162 2 32 38 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 76 162
  (Polychromatic418967fa.accept_12_3_4_6_1_434 63 76 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 76 162 2 31 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 76 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 76 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 76 162 2 30 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 76 162 (accept_3_5 59 76 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 76 162 2 29 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 76 162 (Polychromatic418967fa.accept_12_9_4_6_1_460 57 76 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 76 162 2 28 38 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 76 162
  (Polychromatic418967fa.accept_16_7_12_2_1_8902 55 76 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 76 162 2 27 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 76 162 (accept_3_5 53 76 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 76
  162 2 26 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  76 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 76 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 76 162 2 25 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 76 162 (Polychromatic418967fa.accept_14_7_6_8_1_2856 49 76 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 76 162 2 24 38 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 76 162 (accept_3_5 47 76 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 76 162 2 23 38 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 76 162
  (Polychromatic418967fa.accept_12_9_4_6_1_460 45 76 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 76 162 2 22 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 76 162 (Polychromatic418967fa.accept_13_4_11_6_1_1033 43 76 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 76 162 2 21 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 76 162 (accept_3_5 41 76 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 76 162 2 20 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 76 162 (Polychromatic418967fa.accept_12_3_4_6_1_434 39 76 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 76 162 2 19 38 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 76 162
  (Polychromatic418967fa.accept_7_2_6_1_1_73 37 76 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 76 162 2 18 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 76 162 (accept_3_5 35 76 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 76
  162 2 17 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  76 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 76 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 76 162 2 16 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 76 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 31 76 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 76 162 2 15 38 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 76 162 (accept_3_5 29 76 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 76 162 2 14 38 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 76 162
  (Polychromatic418967fa.accept_12_3_4_6_1_434 27 76 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 76 162 2 13 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 76 162 (Polychromatic418967fa.accept_16_9_12_2_1_3093 25 76 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 76 162 2 12 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 76 162 (accept_3_5 23 76 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76 162 2 11 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 76 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 76 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 76 162 2 10 38 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 76 162
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 76 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 76 162 2 9 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 76 162 (accept_3_5 17 76 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 76
  162 2 8 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  76 162 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 76 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 76 162 2 7 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 76 162 (Polychromatic418967fa.accept_15_13_1_12_1_1638 13 76 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 76 162 2 6 38 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 76 162 (accept_3_5 11 76 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76 162 2 5 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 76 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 76 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 76 162 2 4 38 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 76 162
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 7 76 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 76 162 2 3 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 76 162 (accept_3_5 5 76 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 162
  2 2 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 76
  162 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 76 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 76 162 2 1 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 76 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 76 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 76
  162)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 162 (allA_succ_of_accept
  74 75 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 74 75 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 75 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 75 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 75 162 3 24 25 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 75 162
  (Polychromatic418967fa.accept_16_7_11_2_1_3117 71 75 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 75 162 (Polychromatic418967fa.accept_12_10_3_6_1_882 70 75 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 75 162 3 23 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 75 162 (Polychromatic418967fa.accept_10_8_5_2_1_881 68
  75 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 162
  (Polychromatic418967fa.accept_7_4_5_1_1_418 67 75 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 75 162 3 22 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 75 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 75 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 162 (Polychromatic418967fa.accept_12_4_3_6_1_879 64 75 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 75 162 3 21 25 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 75 162
  (Polychromatic418967fa.accept_7_6_5_1_1_416 62 75 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 75 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 162 3 20 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 59
  75 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 162
  (Polychromatic418967fa.accept_10_8_5_2_1_881 58 75 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 75 162 3 19 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 75 162 (Polychromatic418967fa.accept_12_8_3_6_1_909 56 75 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 75 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 75 162 3 18 25 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 75 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 75 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 75 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 75 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 75 162 3 17 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 75 162 (Polychromatic418967fa.accept_12_2_3_6_1_112 50
  75 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 75 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 75 162 3 16 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 75 162 (Polychromatic418967fa.accept_10_7_5_2_1_880 47 75 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 75 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 162 3 15 25 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 162
  (Polychromatic418967fa.accept_12_8_3_6_1_909 44 75 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 162 (Polychromatic418967fa.accept_10_3_5_2_1_38 43 75 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 75 162 3 14 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 75 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 75
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 162
  (Polychromatic418967fa.accept_12_4_3_6_1_879 40 75 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 75 162 3 13 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 75 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 38 75 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 75 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 75 162 3 12 25 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 75 162
  (Polychromatic418967fa.accept_13_9_10_6_1_1028 35 75 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 75 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 75 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 75 162 3 11 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 75 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 32
  75 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 162
  (Polychromatic418967fa.accept_7_3_5_1_1_72 31 75 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 75 162 3 10 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 75 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 75 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 162 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 75 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 75 162 3 9 25 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 75 162
  (Polychromatic418967fa.accept_12_2_3_6_1_112 26 75 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 75 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 75 162 3 8 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 75 162 (Polychromatic418967fa.accept_10_3_5_2_1_38 23 75 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 162
  (Polychromatic418967fa.accept_12_10_3_6_1_882 22 75 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 75 162 3 7 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 75 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 75 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 162 (Polychromatic418967fa.accept_17_2_7_9_1_2796 19 75 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 75 162 3 6 25 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 75 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 75 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 162 (Polychromatic418967fa.accept_12_4_3_6_1_879 16 75 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 162 3 5 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 162 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 75 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 75 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 75 162 3 4 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 75 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 75 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 75 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 75 162 3 3 25 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 162
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 75 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 162 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 75 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 162 3 2 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 75 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 75 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 162
  (Polychromatic418967fa.accept_7_4_5_1_1_418 4 75 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 75 162 3 1 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 75 162 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 75 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 75 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  162))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 162 (allA_succ_of_accept
  73 74 162 (accept_3_4 73 74 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 74 162 2 36 37 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 74 162
  (Polychromatic418967fa.accept_15_11_14_12_1_2458 71 74 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 74 162 2 35 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 74 162 (Polychromatic418967fa.accept_12_9_2_6_1_455 69 74 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 74 162 2 34 37 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 74 162 (accept_3_4 67 74 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 74 162 2 33 37 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 74 162
  (Polychromatic418967fa.accept_19_8_17_10_1_8900 65 74 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 74 162 2 32 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 74 162 (Polychromatic418967fa.accept_12_3_2_6_1_138 63 74 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 74 162 2 31 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 74 162 (accept_3_4 61 74 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 74 162 2 30 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 74 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 74 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 74 162 2 29 37 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 74 162
  (Polychromatic418967fa.accept_10_7_4_2_1_903 57 74 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 74 162 2 28 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 74 162 (accept_3_4 55 74 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 74
  162 2 27 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  74 162 (Polychromatic418967fa.accept_13_1_9_6_1_146 53 74 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 74 162 2 26 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 74 162 (Polychromatic418967fa.accept_12_3_2_6_1_138 51 74 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 74 162 2 25 37 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 74 162 (accept_3_4 49 74 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 74 162 2 24 37 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 74 162
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 74 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 74 162 2 23 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 74 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 74 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 74 162 2 22 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 74 162 (accept_3_4 43 74 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 74 162 2 21 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 74 162 (Polychromatic418967fa.accept_13_2_9_6_1_501 41 74 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 74 162 2 20 37 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 74 162
  (Polychromatic418967fa.accept_12_3_2_6_1_138 39 74 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 74 162 2 19 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 74 162 (accept_3_4 37 74 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 74
  162 2 18 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  74 162 (Polychromatic418967fa.accept_24_11_2_18_1_8960 35 74 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 74 162 2 17 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 74 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 74 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 74 162 2 16 37 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 74 162 (accept_3_4 31 74 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 74 162 2 15 37 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 74 162
  (Polychromatic418967fa.accept_13_3_9_6_1_502 29 74 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 74 162 2 14 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 74 162 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 74 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 74 162 2 13 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 74 162 (accept_3_4 25 74 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 74 162 2 12 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 74 162 (Polychromatic418967fa.accept_13_10_9_6_1_1026 23 74 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 74 162 2 11 37 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 74 162
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 74 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 74 162 2 10 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 74 162 (accept_3_4 19 74 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 74
  162 2 9 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  74 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 74 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 74 162 2 8 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 74 162 (Polychromatic418967fa.accept_12_3_2_6_1_138 15 74 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 74 162 2 7 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 74 162 (accept_3_4 13 74 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74 162 2 6 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 74 162 (Polychromatic418967fa.accept_14_11_4_8_1_664 11 74 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 74 162 2 5 37 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 74 162
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 74 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 74 162 2 4 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 74 162 (accept_3_4 7 74 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 162
  2 3 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 74
  162 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 74 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 74 162 2 2 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 74 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 74 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 74 162 2 1 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 74 162 (accept_3_4 1 74 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 74 162)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73
  162 (allA_succ_of_accept 72 73 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 73 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 73 162 (accept_3_5 71 73 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 73 162 (Polychromatic418967fa.accept_11_4_7_8_1_1926 70 73 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 73 162 (Polychromatic418967fa.accept_20_9_13_2_1_8908
  69 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 162 (accept_3_5 68
  73 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 67 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 73 162 (Polychromatic418967fa.accept_13_1_8_6_1_1016 66 73 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 73 162 (accept_3_5 65 73 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 73 162 (Polychromatic418967fa.accept_17_13_5_9_1_1762 64 73 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 73 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 73 162 (accept_3_5 62 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  73 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 73 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 73 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 73 162 (accept_3_5 59 73 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 73 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 58 73 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 73 162
  (Polychromatic418967fa.accept_30_27_13_12_1_4443 57 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 73 162 (accept_3_5 56 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 73 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 73 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 73 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 73 162 (accept_3_5 53 73 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 73 162
  (Polychromatic418967fa.accept_25_2_23_12_1_8959 52 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 73 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 73 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 162 (accept_3_5 50 73 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 73 162 (Polychromatic418967fa.accept_16_1_9_2_1_4161 49 73 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 162 (Polychromatic418967fa.accept_11_4_7_8_1_1926
  48 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 73 162 (accept_3_5 47
  73 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 73 162
  (Polychromatic418967fa.accept_7_4_3_1_1_87 46 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 73 162 (Polychromatic418967fa.accept_10_5_3_2_1_899 45 73 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 162 (accept_3_5 44 73 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 73 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 73 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 162
  (Polychromatic418967fa.accept_19_4_16_10_1_2171 42 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 162 (accept_3_5 41 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 73 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 162 (accept_3_5 38 73 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 73 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 162
  (Polychromatic418967fa.accept_24_12_1_18_1_8958 36 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 162 (accept_3_5 35 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 162 (Polychromatic418967fa.accept_22_12_7_8_1_8957 34 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 73 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 162 (accept_3_5 32 73 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 73 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 162
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 162 (accept_3_5 29 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 162 (Polychromatic418967fa.accept_13_2_8_6_1_2390 28 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 73 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 162 (accept_3_5 26 73 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 73 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 162
  (Polychromatic418967fa.accept_13_11_8_6_1_1023 24 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 162 (accept_3_5 23 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 162 (Polychromatic418967fa.accept_16_6_9_2_1_6518 22 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 162 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 73 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 162 (accept_3_5 20 73 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 73 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 162
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 162 (accept_3_5 17 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 73 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 162 (accept_3_5 14 73 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 162 (Polychromatic418967fa.accept_17_13_5_9_1_1762 13 73 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 162
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 162 (accept_3_5 11 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 162 (Polychromatic418967fa.accept_15_10_13_12_1_3384 10 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 73 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 162 (accept_3_5 8 73 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 73 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 162
  (Polychromatic418967fa.accept_16_6_9_2_1_6518 6 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 162 (accept_3_5 5 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  162 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 73 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 73 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 162 (accept_3_5 2 73 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 162 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 73 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  162))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 162 (allA_succ_of_accept 71
  72 162 (Polychromatic418967fa.accept_14_1_2_8_1_655 71 72 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 72 162 2 35 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 69 72 162 3 23 24 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 72 162 2 34 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 72 162 (Polychromatic418967fa.accept_20_7_12_2_1_4465 67 72 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 162 6 11 12 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 162
  (Polychromatic418967fa.accept_17_14_4_9_1_2792 65 72 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 72 162 2 32 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 72 162 9 7 8 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 72 162 2 31 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 72 162 (Polychromatic418967fa.accept_13_9_7_6_1_1673 61 72 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 162 6 10 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 59
  72 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72 162 2 29 36 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 72 162 3 19 24 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 72 162 2 28 36 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 72 162
  (Polychromatic418967fa.accept_7_6_2_1_1_214 55 72 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 72 162 18 3 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 72 162 (Polychromatic418967fa.accept_13_1_7_6_1_142 53 72 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 72 162 2 26 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 72 162 3 17 24 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 72 162 2 25 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 162
  (Polychromatic418967fa.accept_19_11_15_10_1_7406 49 72 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 72 162 6 8 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 72 162 (Polychromatic418967fa.accept_11_3_6_8_1_1924 47 72 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 162 2 23 36 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 72 162 9 5 8 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 72 162 2 22 36 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 72 162
  (Polychromatic418967fa.accept_13_4_7_6_1_2359 43 72 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 72 162 6 7 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 72 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 72 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 72 162 2 20 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 72 162 3 13 24 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 72 162 2 19 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 162 (Polychromatic418967fa.accept_20_17_12_2_1_8956
  37 72 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 162 18 2 4 9 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 162
  (Polychromatic418967fa.accept_13_9_7_6_1_1673 35 72 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 72 162 2 17 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 72 162 3 11 24 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 72 162 2 16 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 72 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 72 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 162 6 5 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 162 (Polychromatic418967fa.accept_14_1_2_8_1_655 29 72 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 162 2 14 36 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 72 162 9 3 8 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 72 162 2 13 36 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 162
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 25 72 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 72 162 6 4 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 72 162 (Polychromatic418967fa.accept_19_4_15_10_1_4602 23 72 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 162 2 11 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 72 162 3 7 24 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 72 162 2 10 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 72 162 (Polychromatic418967fa.accept_17_2_4_9_1_2791
  19 72 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 162 18 1 4 9 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 162
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 72 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 72 162 2 8 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 72 162 3 5 24 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 72 162 2 7 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 72 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 72 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 162 6 2 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 162 (Polychromatic418967fa.accept_19_11_15_10_1_7406 11 72
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 162 2 5 36 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 72 162 9 1 8 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 72 162 2 4 36 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 162
  (Polychromatic418967fa.accept_20_7_12_2_1_4465 7 72 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 72 162 6 1 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 72 162 (Polychromatic418967fa.accept_19_5_15_10_1_7405 5 72 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 162 2 2 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 72 162 3 1 24 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 72 162 2 1 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 162 (Polychromatic418967fa.accept_13_1_7_6_1_142 1 72 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  162)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 162 (allA_succ_of_accept 70
  71 162 (accept_3_4 70 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 71 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 71 162 (Polychromatic418967fa.accept_11_2_5_8_1_470 68 71 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 162 (accept_3_4 67 71 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 71 162 (Polychromatic418967fa.accept_10_6_1_2_1_874 66 71 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 65
  71 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 71 162 (accept_3_4 64 71
  162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 71 162
  (Polychromatic418967fa.accept_10_3_1_2_1_521 63 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 71 162 (Polychromatic418967fa.accept_17_11_3_9_1_6387 62 71 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 162 (accept_3_4 61 71 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 71 162 (Polychromatic418967fa.accept_16_12_7_2_1_4159 60 71 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 162
  (Polychromatic418967fa.accept_10_9_1_2_1_522 59 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 162 (accept_3_4 58 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 162 (Polychromatic418967fa.accept_10_6_1_2_1_874 56 71 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 162 (accept_3_4 55 71 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 162 (Polychromatic418967fa.accept_21_12_8_15_1_8955 54 71 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 162 (accept_3_4 52 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 162 (Polychromatic418967fa.accept_14_9_1_8_1_2849 51 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 162 (Polychromatic418967fa.accept_19_12_14_10_1_4625 50 71 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 162 (accept_3_4 49 71 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 162 (Polychromatic418967fa.accept_21_6_8_15_1_8903 48 71
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 162
  (Polychromatic418967fa.accept_11_3_5_8_1_458 47 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 162 (accept_3_4 46 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 162 (Polychromatic418967fa.accept_14_2_1_8_1_650 44 71 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 162 (accept_3_4 43 71 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 162 (Polychromatic418967fa.accept_19_4_14_10_1_7467 42 71 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 162 (accept_3_4 40 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 162 (Polychromatic418967fa.accept_10_9_1_2_1_522 39 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 162 (Polychromatic418967fa.accept_15_8_11_12_1_1626 38 71 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 162 (accept_3_4 37 71 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 162 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 71 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 162
  (Polychromatic418967fa.accept_11_2_5_8_1_470 35 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 162 (accept_3_4 34 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 162 (Polychromatic418967fa.accept_22_10_5_8_1_8954 32 71 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 162 (accept_3_4 31 71 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 162 (Polychromatic418967fa.accept_14_2_1_8_1_650 30 71 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 162 (accept_3_4 28 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 162 (Polychromatic418967fa.accept_16_11_7_2_1_4185 27 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 162 (Polychromatic418967fa.accept_10_6_1_2_1_874 26 71 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 162 (accept_3_4 25 71 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 162 (Polychromatic418967fa.accept_11_2_5_8_1_470 24 71 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 162
  (Polychromatic418967fa.accept_10_3_1_2_1_521 23 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 162 (accept_3_4 22 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 162 (Polychromatic418967fa.accept_19_1_14_10_1_4619 20 71 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 162 (accept_3_4 19 71 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 162 (Polychromatic418967fa.accept_17_1_3_9_1_958 18 71 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 162 (accept_3_4 16 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 162 (Polychromatic418967fa.accept_19_15_14_10_1_4667 15 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 162 (Polychromatic418967fa.accept_11_3_5_8_1_458 14 71 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 162 (accept_3_4 13 71 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 162 (Polychromatic418967fa.accept_16_12_7_2_1_4159 12 71 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 162
  (Polychromatic418967fa.accept_16_11_7_2_1_4185 11 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 162 (accept_3_4 10 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 71 162 (Polychromatic418967fa.accept_15_8_11_12_1_1626 8 71 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 162 (accept_3_4 7 71 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 71 162 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 71 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 71
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 162 (accept_3_4 4 71 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71 162 (Polychromatic418967fa.accept_10_3_1_2_1_521 3
  71 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 162
  (Polychromatic418967fa.accept_11_2_5_8_1_470 2 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 71 162 (accept_3_4 1 71 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71
  162))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 162 (allA_succ_of_accept 69
  70 162 (Polychromatic418967fa.accept_12_9_10_6_1_872 69 70 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 70 162 2 34 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 70 162 (Polychromatic418967fa.accept_11_1_4_8_1_1918 67 70 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 70 162 2 33 35 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 70 162 (accept_3_5 65 70 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 70 162 2 32 35 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 70 162
  (Polychromatic418967fa.accept_12_3_10_6_1_442 63 70 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 70 162 2 31 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 70 162 (Polychromatic418967fa.accept_19_4_13_10_1_7382 61 70 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 70 162 2 30 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 70 162 (accept_3_5 59 70 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 70 162 2 29 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 70 162 (Polychromatic418967fa.accept_12_9_10_6_1_872 57 70 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 70 162 2 28 35 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 70 162
  (Polychromatic418967fa.accept_13_3_5_6_1_3192 55 70 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 70 162 2 27 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 70 162 (accept_3_5 53 70 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 70
  162 2 26 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  70 162 (Polychromatic418967fa.accept_11_7_4_8_1_1371 51 70 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 70 162 2 25 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 70 162 (Polychromatic418967fa.accept_13_10_5_6_1_1671 49 70 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 70 162 2 24 35 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 70 162 (accept_3_5 47 70 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 70 162 2 23 35 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 70 162
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 70 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 70 162 2 22 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 70 162 (Polychromatic418967fa.accept_13_4_5_6_1_3201 43 70 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 70 162 2 21 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 70 162 (accept_3_5 41 70 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70 162 2 20 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 70 162 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 70 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 70 162 2 19 35 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 70 162
  (Polychromatic418967fa.accept_13_11_5_6_1_519 37 70 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 70 162 2 18 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 70 162 (accept_3_5 35 70 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 70
  162 2 17 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  70 162 (Polychromatic418967fa.accept_12_9_10_6_1_872 33 70 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 70 162 2 16 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 70 162 (Polychromatic418967fa.accept_21_10_7_15_1_8930 31 70 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 162 2 15 35 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 162 (accept_3_5 29 70 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70 162 2 14 35 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 70 162
  (Polychromatic418967fa.accept_12_3_10_6_1_442 27 70 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 70 162 2 13 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 70 162 (Polychromatic418967fa.accept_13_12_5_6_1_1050 25 70 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 70 162 2 12 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 70 162 (accept_3_5 23 70 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70 162 2 11 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 70 162 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 70 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 70 162 2 10 35 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 70 162
  (Polychromatic418967fa.accept_16_3_6_2_1_4157 19 70 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 70 162 2 9 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 70 162 (accept_3_5 17 70 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 70
  162 2 8 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  70 162 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 70 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 70 162 2 7 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 70 162 (Polychromatic418967fa.accept_15_13_10_12_1_2503 13 70 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 70 162 2 6 35 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 70 162 (accept_3_5 11 70 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 162 2 5 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 70 162 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 70 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 70 162 2 4 35 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 70 162
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 70 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 70 162 2 3 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 70 162 (accept_3_5 5 70 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 70 162
  2 2 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 70
  162 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 70 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 70 162 2 1 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 70 162 (Polychromatic418967fa.accept_11_1_4_8_1_1918 1 70 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  162)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 162 (allA_succ_of_accept 68 69
  162 (Polychromatic418967fa.accept_7_5_6_1_1_407 68 69 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 69 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 69 162 3 22 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 69 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 65
  69 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 162
  (Polychromatic418967fa.accept_12_4_9_6_1_440 64 69 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 69 162 3 21 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 69 162 (Polychromatic418967fa.accept_12_2_9_6_1_439 62 69 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 69 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 69 162 3 20 23 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 69 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 69 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 69 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 58 69 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 69 162 3 19 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 69 162 (Polychromatic418967fa.accept_12_8_9_6_1_127 56
  69 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 55 69 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 69 162 3 18 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 69 162 (Polychromatic418967fa.accept_20_13_9_2_1_5933 53 69 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 162 (Polychromatic418967fa.accept_12_4_9_6_1_440 52 69 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 69 162 3 17 23 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 69 162
  (Polychromatic418967fa.accept_11_6_3_8_1_843 50 69 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 162 (Polychromatic418967fa.accept_11_5_3_8_1_454 49 69 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 69 162 3 16 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 69 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  69 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 162
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 46 69 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 69 162 3 15 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 69 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 69 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 69 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 69 162 3 14 23 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 69 162
  (Polychromatic418967fa.accept_10_1_9_2_1_45 41 69 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 69 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 69 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 69 162 3 13 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 69 162 (Polychromatic418967fa.accept_11_5_3_8_1_454 38
  69 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 162
  (Polychromatic418967fa.accept_7_2_6_1_1_73 37 69 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 69 162 3 12 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 69 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 69 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 162 (Polychromatic418967fa.accept_12_10_9_6_1_1445 34 69
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 69 162 3 11 23 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 69 162
  (Polychromatic418967fa.accept_12_8_9_6_1_127 32 69 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 69 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 69 162 3 10 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 162 (Polychromatic418967fa.accept_15_14_9_12_1_2498
  29 69 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 162
  (Polychromatic418967fa.accept_11_6_3_8_1_843 28 69 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 69 162 3 9 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 69 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 69 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 162 (Polychromatic418967fa.accept_15_10_9_12_1_2497 25 69
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 69 162 3 8 23 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 69 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 69 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 69 162 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 69 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 162 3 7 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 162 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 69 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 69 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 69 162 3 6 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 69 162 (Polychromatic418967fa.accept_10_7_9_2_1_1887 17 69 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 69 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 69 162 3 5 23 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 69 162
  (Polychromatic418967fa.accept_12_2_9_6_1_439 14 69 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 162 (Polychromatic418967fa.accept_16_13_5_2_1_2131 13 69 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 162 3 4 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 69 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 162
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 69 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 69 162 3 3 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 69 162 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 69 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 69 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 69 162 3 2 23 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 69 162
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 69 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 69 162 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 69 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 162 3 1 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 69 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 162
  (Polychromatic418967fa.accept_10_1_9_2_1_45 1 69 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 69 162))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 162
  (allA_succ_of_accept 67 68 162 (accept_3_4 67 68 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 68
  162 2 33 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65
  68 162 (Polychromatic418967fa.accept_10_5_8_2_1_517 65 68 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 68 162 2 32 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 68 162 (Polychromatic418967fa.accept_12_3_8_6_1_895 63 68 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 68 162 2 31 34 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 68 162 (accept_3_4 61 68 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 68 162 2 30 34 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 68 162
  (Polychromatic418967fa.accept_7_3_5_1_1_72 59 68 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 68 162 2 29 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 68 162 (Polychromatic418967fa.accept_12_9_8_6_1_466 57 68 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 68 162 2 28 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 68 162 (accept_3_4 55 68 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 68 162 2 27 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 68 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 68 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 68 162 2 26 34 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 68 162
  (Polychromatic418967fa.accept_12_3_8_6_1_895 51 68 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 68 162 2 25 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 68 162 (accept_3_4 49 68 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 68
  162 2 24 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  68 162 (Polychromatic418967fa.accept_32_15_4_2_1_8953 47 68 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 68 162 2 23 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 68 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 68 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 68 162 2 22 34 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 68 162 (accept_3_4 43 68 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68 162 2 21 34 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 68 162
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 68 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 68 162 2 20 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 68 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 68 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 68 162 2 19 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 68 162 (accept_3_4 37 68 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68 162 2 18 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 68 162 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 68 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 68 162 2 17 34 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 68 162
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 68 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 68 162 2 16 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 68 162 (accept_3_4 31 68 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68
  162 2 15 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  68 162 (Polychromatic418967fa.accept_21_8_5_15_1_4208 29 68 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 68 162 2 14 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 68 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 68 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 68 162 2 13 34 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 68 162 (accept_3_4 25 68 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68 162 2 12 34 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 68 162
  (Polychromatic418967fa.accept_13_10_3_6_1_1003 23 68 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 68 162 2 11 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 68 162 (Polychromatic418967fa.accept_12_9_8_6_1_466 21 68 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 68 162 2 10 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 68 162 (accept_3_4 19 68 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68 162 2 9 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 68 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 68 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 68 162 2 8 34 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 68 162
  (Polychromatic418967fa.accept_10_5_8_2_1_517 15 68 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 68 162 2 7 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 68 162 (accept_3_4 13 68 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68
  162 2 6 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  68 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 68 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 68 162 2 5 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 68 162 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 68 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 68 162 2 4 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 68 162 (accept_3_4 7 68 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 162 2 3 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 68 162 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 68 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 68 162 2 2 34 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 68 162
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 68 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 68 162 2 1 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 68 162 (accept_3_4 1 68 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  162)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 162 (allA_succ_of_accept 66 67
  162 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 162 (accept_3_5 65 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 162 (Polychromatic418967fa.accept_10_4_7_2_1_211 64 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 162 (Polychromatic418967fa.accept_15_3_7_12_1_372 63 67 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 162 (accept_3_5 62 67 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 67 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 162
  (Polychromatic418967fa.accept_13_8_2_6_1_2385 60 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 162 (accept_3_5 59 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 162 (Polychromatic418967fa.accept_20_18_7_2_1_4449 58 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 67 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 162 (accept_3_5 56 67 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 162 (Polychromatic418967fa.accept_10_5_7_2_1_516 55 67 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 162
  (Polychromatic418967fa.accept_7_5_4_1_1_412 54 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 162 (accept_3_5 53 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 162 (Polychromatic418967fa.accept_13_12_2_6_1_2396 51 67 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 162 (accept_3_5 50 67 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 67 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 162
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 48 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 162 (accept_3_5 47 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 162 (Polychromatic418967fa.accept_14_4_11_8_1_2034 46 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 67 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 162 (accept_3_5 44 67 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 162 (Polychromatic418967fa.accept_13_4_2_6_1_1043 43 67 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 162
  (Polychromatic418967fa.accept_17_8_16_9_1_8952 42 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 162 (accept_3_5 41 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 162 (Polychromatic418967fa.accept_10_9_7_2_1_887 39 67 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 162 (accept_3_5 38 67 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 67 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 162
  (Polychromatic418967fa.accept_13_10_2_6_1_1044 36 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 162 (accept_3_5 35 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 162 (Polychromatic418967fa.accept_10_4_7_2_1_211 34 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 67 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 162 (accept_3_5 32 67 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 67 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 162
  (Polychromatic418967fa.accept_13_4_2_6_1_1043 30 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 162 (accept_3_5 29 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 162 (Polychromatic418967fa.accept_25_3_17_12_1_8951 28 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 162 (Polychromatic418967fa.accept_13_1_2_6_1_515 27 67 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 162 (accept_3_5 26 67 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 67 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 162
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 162 (accept_3_5 23 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 162 (Polychromatic418967fa.accept_13_9_2_6_1_514 22 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 67 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 162 (accept_3_5 20 67 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 67 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 162
  (Polychromatic418967fa.accept_14_4_11_8_1_2034 18 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 162 (accept_3_5 17 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 162 (Polychromatic418967fa.accept_24_16_19_18_1_8950 16 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 162 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 67 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 162 (accept_3_5 14 67 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 67 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 162
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 162 (accept_3_5 11 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 67 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 162 (accept_3_5 8 67 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 162 (Polychromatic418967fa.accept_22_7_1_8_1_8949 7 67 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 162
  (Polychromatic418967fa.accept_15_6_7_12_1_869 6 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 162 (accept_3_5 5 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  162 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 67 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 67 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 162 (accept_3_5 2 67 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 67 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  162))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 162 (allA_succ_of_accept 65 66
  162 (Polychromatic418967fa.accept_7_2_3_1_1_10 65 66 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 66 162 2 32 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 66 162 3 21 22 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 66 162 2 31 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 66 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 66 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 162 6 10 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 162 (Polychromatic418967fa.accept_13_7_1_6_1_3287
  59 66 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 162 2 29 33 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 66 162 3 19 22 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 66 162 2 28 33 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 66 162
  (Polychromatic418967fa.accept_13_3_1_6_1_509 55 66 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 66 162 6 9 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 66 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 66 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66 162 2 26 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 66 162 3 17 22 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 66 162 2 25 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 66 162 (Polychromatic418967fa.accept_21_7_3_15_1_5800
  49 66 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 162 6 8 11 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 162
  (Polychromatic418967fa.accept_7_5_3_1_1_424 47 66 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 66 162 2 23 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 66 162 3 15 22 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 66 162 2 22 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 66 162 (Polychromatic418967fa.accept_21_1_3_15_1_5797 43 66 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 162 6 7 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 41 66 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 162 2 20 33 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 66 162 3 13 22 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 66 162 2 19 33 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 162
  (Polychromatic418967fa.accept_7_2_3_1_1_10 37 66 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 162 6 6 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 66 162 (Polychromatic418967fa.accept_13_9_1_6_1_510 35 66 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 162 2 17 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 66 162 3 11 22 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 66 162 2 16 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 31
  66 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 162 6 5 11 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 162
  (Polychromatic418967fa.accept_13_3_1_6_1_509 29 66 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 66 162 2 14 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 66 162 3 9 22 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 66 162 2 13 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 66 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 66 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 162 6 4 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 66 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 162 2 11 33 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 66 162 3 7 22 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 66 162 2 10 33 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 162
  (Polychromatic418967fa.accept_7_5_3_1_1_424 19 66 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 162 6 3 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 162 (Polychromatic418967fa.accept_15_2_6_12_1_1613 17 66 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 162 2 8 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 66 162 3 5 22 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 66 162 2 7 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 162 (Polychromatic418967fa.accept_19_13_9_10_1_2181 13 66
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 162 6 2 11 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 162
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 66 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 66 162 2 5 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 66 162 3 3 22 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 66 162 2 4 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 66 162 (Polychromatic418967fa.accept_13_7_1_6_1_3287 7 66 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 162 6 1 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 66 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 162 2 2 33 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 66 162 3 1 22 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 66 162 2 1 33 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 162
  (Polychromatic418967fa.accept_10_1_6_2_1_867 1 66 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 66 162)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 162
  (allA_succ_of_accept 64 65 162 (accept_3_4 64 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  65 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 65 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 62 65 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 162 (accept_3_4 61 65 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 162 (Polychromatic418967fa.accept_16_12_1_2_1_2163 60 65 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 162 (accept_3_4 58 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 162 (Polychromatic418967fa.accept_10_7_5_2_1_880 57 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 162 (Polychromatic418967fa.accept_17_5_14_9_1_5104 56 65 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 162 (accept_3_4 55 65 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 162 (Polychromatic418967fa.accept_15_9_5_12_1_1640 54 65
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 162
  (Polychromatic418967fa.accept_10_3_5_2_1_38 53 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 162 (accept_3_4 52 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 162 (Polychromatic418967fa.accept_19_12_8_10_1_8948 50 65 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 162 (accept_3_4 49 65 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 65 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 162 (accept_3_4 46 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 162 (Polychromatic418967fa.accept_16_12_1_2_1_2163 44 65 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 162 (accept_3_4 43 65 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 162 (Polychromatic418967fa.accept_11_9_10_8_1_444 42 65 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 162
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 162 (accept_3_4 40 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 65 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 162 (accept_3_4 37 65 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 162 (Polychromatic418967fa.accept_15_6_5_12_1_1642 36 65 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 162 (accept_3_4 34 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 162 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 162 (Polychromatic418967fa.accept_15_2_5_12_1_369 32 65 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 162 (accept_3_4 31 65 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 162 (Polychromatic418967fa.accept_19_11_8_10_1_8901 30 65 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 162
  (Polychromatic418967fa.accept_14_1_9_8_1_2863 29 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 162 (accept_3_4 28 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 162 (Polychromatic418967fa.accept_22_4_21_8_1_8923 26 65 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 162 (accept_3_4 25 65 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 65 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 162 (accept_3_4 22 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 162 (Polychromatic418967fa.accept_15_6_5_12_1_1642 21 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 65 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 162 (accept_3_4 19 65 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 162 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 65 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 162
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 162 (accept_3_4 16 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 162 (Polychromatic418967fa.accept_22_14_21_8_1_8947 14 65 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 162 (accept_3_4 13 65 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 162 (Polychromatic418967fa.accept_16_12_1_2_1_2163 12 65
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 162 (accept_3_4 10 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 162 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 162 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 65 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 162 (accept_3_4 7 65 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 65 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 162
  (Polychromatic418967fa.accept_17_5_14_9_1_5104 5 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 162 (accept_3_4 4 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  162 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 65 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 162 (Polychromatic418967fa.accept_15_2_5_12_1_369 2 65 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 162 (accept_3_4 1 65 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 162))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 162
  (allA_succ_of_accept 63 64 162 (Polychromatic418967fa.accept_12_3_4_6_1_434 63 64 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 64 162 2 31 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 64 162 (Polychromatic418967fa.accept_15_1_4_12_1_2401
  61 64 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 64 162 2 30 32 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 64 162 (accept_3_5 59
  64 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 64 162 2 29 32 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 64 162
  (Polychromatic418967fa.accept_10_7_4_2_1_903 57 64 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 64 162 2 28 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 64 162 (Polychromatic418967fa.accept_17_4_13_9_1_921 55 64 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 64 162 2 27 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 64 162 (accept_3_5 53 64 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 64 162 2 26 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 64 162 (Polychromatic418967fa.accept_12_3_4_6_1_434 51 64 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 64 162 2 25 32 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 64 162
  (Polychromatic418967fa.accept_13_10_12_6_1_991 49 64 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 64 162 2 24 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 64 162 (accept_3_5 47 64 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 64
  162 2 23 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  64 162 (Polychromatic418967fa.accept_12_9_4_6_1_460 45 64 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 64 162 2 22 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 64 162 (Polychromatic418967fa.accept_11_10_9_8_1_1974 43 64 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 64 162 2 21 32 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 64 162 (accept_3_5 41 64 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 64 162 2 20 32 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 64 162
  (Polychromatic418967fa.accept_12_3_4_6_1_434 39 64 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 64 162 2 19 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 64 162 (Polychromatic418967fa.accept_10_7_4_2_1_903 37 64 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 64 162 2 18 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 64 162 (accept_3_5 35 64 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 64 162 2 17 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 64 162 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 64 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 64 162 2 16 32 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 64 162
  (Polychromatic418967fa.accept_13_5_12_6_1_508 31 64 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 64 162 2 15 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 64 162 (accept_3_5 29 64 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64
  162 2 14 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  64 162 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 64 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 64 162 2 13 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 64 162 (Polychromatic418967fa.accept_20_5_4_2_1_5912 25 64 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 64 162 2 12 32 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 64 162 (accept_3_5 23 64 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64 162 2 11 32 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 64 162
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 64 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 64 162 2 10 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 64 162 (Polychromatic418967fa.accept_20_19_4_2_1_8946 19 64 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 64 162 2 9 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 64 162 (accept_3_5 17 64 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 64 162 2 8 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 64 162 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 64 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 64 162 2 7 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 64 162 (Polychromatic418967fa.accept_23_13_18_1_1_8945
  13 64 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 162 2 6 32 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 162 (accept_3_5 11
  64 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64 162 2 5 32 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 64 162
  (Polychromatic418967fa.accept_12_9_4_6_1_460 9 64 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 64 162 2 4 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 64 162 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 64 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 162 2 3 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 162 (accept_3_5 5 64 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 64 162 2 2 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 64 162 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 64 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 64 162 2 1 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 64 162 (Polychromatic418967fa.accept_15_1_4_12_1_2401 1
  64 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  162)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 162 (allA_succ_of_accept 62 63 162
  (Polychromatic418967fa.accept_12_2_3_6_1_112 62 63 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 63 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 63 162 3 20 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 63 162 (Polychromatic418967fa.accept_19_2_6_10_1_3364
  59 63 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 162
  (Polychromatic418967fa.accept_12_10_3_6_1_882 58 63 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 63 162 3 19 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 63 162 (Polychromatic418967fa.accept_12_8_3_6_1_909 56 63 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 162 (Polychromatic418967fa.accept_10_5_3_2_1_899 55 63 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 63 162 9 6 7 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 63 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 63 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 63 162 (Polychromatic418967fa.accept_12_4_3_6_1_879 52 63 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 63 162 3 17 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 63 162 (Polychromatic418967fa.accept_12_2_3_6_1_112 50
  63 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 63 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 63 162 3 16 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 63 162 (Polychromatic418967fa.accept_13_8_11_6_1_1035 47 63 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 162 (Polychromatic418967fa.accept_12_10_3_6_1_882 46 63 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 63 162 9 5 7 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 63 162
  (Polychromatic418967fa.accept_12_8_3_6_1_909 44 63 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 162 (Polychromatic418967fa.accept_13_4_11_6_1_1033 43 63 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 162 3 14 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 63
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 162
  (Polychromatic418967fa.accept_12_4_3_6_1_879 40 63 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 63 162 3 13 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 63 162 (Polychromatic418967fa.accept_12_2_3_6_1_112 38 63 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 63 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 63 162 9 4 7 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 63 162
  (Polychromatic418967fa.accept_10_5_3_2_1_899 35 63 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 63 162 (Polychromatic418967fa.accept_12_10_3_6_1_882 34 63 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 63 162 3 11 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 63 162 (Polychromatic418967fa.accept_12_8_3_6_1_909 32
  63 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 162
  (Polychromatic418967fa.accept_10_1_3_2_1_220 31 63 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 63 162 3 10 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 63 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 63 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 162 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 63 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 63 162 9 3 7 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 63 162
  (Polychromatic418967fa.accept_12_2_3_6_1_112 26 63 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 63 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 63 162 3 8 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 63 162 (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 63 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 162
  (Polychromatic418967fa.accept_12_10_3_6_1_882 22 63 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 63 162 3 7 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 63 162 (Polychromatic418967fa.accept_12_8_3_6_1_909 20 63 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 162 (Polychromatic418967fa.accept_16_3_15_2_1_6475 19 63
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 63 162 9 2 7 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 63 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 63 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 63 162 (Polychromatic418967fa.accept_12_4_3_6_1_879 16 63 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 162 3 5 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 63 162 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 63 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 63 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 63 162 3 4 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 63 162 (Polychromatic418967fa.accept_10_1_3_2_1_220 11 63 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 162 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 63 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 162 9 1 7 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 162
  (Polychromatic418967fa.accept_12_8_3_6_1_909 8 63 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 162 (Polychromatic418967fa.accept_15_7_3_12_1_365 7 63 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 63 162 3 2 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 63 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 162
  (Polychromatic418967fa.accept_12_4_3_6_1_879 4 63 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 63 162 3 1 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 63 162 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 63 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 63 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  162))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 162 (allA_succ_of_accept 61 62 162
  (accept_3_4 61 62 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 62 162 2 30 31 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 62 162
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 59 62 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 62 162 2 29 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 62 162 (Polychromatic418967fa.accept_12_9_2_6_1_455 57 62 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 162 2 28 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 162 (accept_3_4 55 62 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 162 2 27 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 162 (Polychromatic418967fa.accept_17_2_11_9_1_1739 53 62 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 62 162 2 26 31 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 162
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 62 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 62 162 2 25 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 62 162 (accept_3_4 49 62 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 62
  162 2 24 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  62 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 62 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 62 162 2 23 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 62 162 (Polychromatic418967fa.accept_12_9_2_6_1_455 45 62 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 62 162 2 22 31 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 62 162 (accept_3_4 43 62 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 62 162 2 21 31 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 62 162
  (Polychromatic418967fa.accept_13_2_10_6_1_1676 41 62 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 62 162 2 20 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 62 162 (Polychromatic418967fa.accept_12_3_2_6_1_138 39 62 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 62 162 2 19 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 62 162 (accept_3_4 37 62 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 62 162 2 18 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 62 162 (Polychromatic418967fa.accept_13_9_10_6_1_1028 35 62 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 162 2 17 31 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 162
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 62 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 162 2 16 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 62 162 (accept_3_4 31 62 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 62
  162 2 15 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  62 162 (Polychromatic418967fa.accept_13_3_10_6_1_2382 29 62 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 62 162 2 14 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 62 162 (Polychromatic418967fa.accept_12_3_2_6_1_138 27 62 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 62 162 2 13 31 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 62 162 (accept_3_4 25 62 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62 162 2 12 31 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 62 162
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 62 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 62 162 2 11 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 62 162 (Polychromatic418967fa.accept_12_9_2_6_1_455 21 62 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 62 162 2 10 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 62 162 (accept_3_4 19 62 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 62 162 2 9 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 62 162 (Polychromatic418967fa.accept_13_4_10_6_1_989 17 62 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 162 2 8 31 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 162
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 62 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 62 162 2 7 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 62 162 (accept_3_4 13 62 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62
  162 2 6 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  62 162 (Polychromatic418967fa.accept_19_11_5_10_1_8944 11 62 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 62 162 2 5 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 62 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 62 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 162 2 4 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 162 (accept_3_4 7 62 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 62 162 2 3 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 62 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 62 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 162 2 2 31 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 162
  (Polychromatic418967fa.accept_12_3_2_6_1_138 3 62 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 62 162 2 1 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 62 162 (accept_3_4 1 62 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  162)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 162 (allA_succ_of_accept 60 61 162
  (Polychromatic418967fa.accept_7_4_5_1_1_418 60 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 162 (accept_3_5 59 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 162 (Polychromatic418967fa.accept_11_3_6_8_1_1924 58 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 162 (Polychromatic418967fa.accept_22_13_17_8_1_8943 57 61 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 162 (accept_3_5 56 61 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 61 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 162
  (Polychromatic418967fa.accept_13_2_9_6_1_501 54 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 162 (accept_3_5 53 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 61 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 162 (accept_3_5 50 61 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 162 (Polychromatic418967fa.accept_10_9_1_2_1_522 49 61 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 162
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 162 (accept_3_5 47 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 61 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 162 (accept_3_5 44 61 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 61 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 162
  (Polychromatic418967fa.accept_13_3_9_6_1_502 42 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 162 (accept_3_5 41 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 162 (Polychromatic418967fa.accept_13_1_9_6_1_146 40 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 61 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 162 (accept_3_5 38 61 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 162 (Polychromatic418967fa.accept_16_5_13_2_1_2138 37 61 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 162
  (Polychromatic418967fa.accept_10_6_1_2_1_874 36 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 162 (accept_3_5 35 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 162 (Polychromatic418967fa.accept_10_3_1_2_1_521 33 61 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 162 (accept_3_5 32 61 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 61 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 162
  (Polychromatic418967fa.accept_13_4_9_6_1_2376 30 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 162 (accept_3_5 29 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 162 (Polychromatic418967fa.accept_13_2_9_6_1_501 28 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 61 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 162 (accept_3_5 26 61 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 61 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 162
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 162 (accept_3_5 23 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 162 (Polychromatic418967fa.accept_21_1_19_15_1_8914 22 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 162 (Polychromatic418967fa.accept_16_5_13_2_1_2138 21 61 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 162 (accept_3_5 20 61 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 61 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 162
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 162 (accept_3_5 17 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 162 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 61 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 162 (accept_3_5 14 61 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 61 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 162
  (Polychromatic418967fa.accept_21_12_19_15_1_8942 12 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 61 162 (accept_3_5 11 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 61 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 61 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 61 162 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 61 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 162 (accept_3_5 8 61 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 61
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 162
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 162 (accept_3_5 5 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  162 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 61 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 61 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 162 (accept_3_5 2 61 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 162 (Polychromatic418967fa.accept_13_1_9_6_1_146 1 61 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 162)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 162 (allA_succ_of_accept 59 60 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 60 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 60 162 2 29 30 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 60 162 3 19 20 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 60 162 2 28 30 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 162
  (Polychromatic418967fa.accept_16_7_12_2_1_8902 55 60 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 60 162 6 9 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 60 162 (Polychromatic418967fa.accept_13_1_8_6_1_1016 53 60 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 162 2 26 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 60 162 3 17 20 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 60 162 2 25 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 162 (Polychromatic418967fa.accept_16_1_12_2_1_2136
  49 60 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 162 6 8 10 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 162
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 60 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 60 162 2 23 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 60 162 3 15 20 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 60 162 2 22 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 60 162 (Polychromatic418967fa.accept_19_5_3_10_1_4641 43 60 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 162 6 7 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 162 (Polychromatic418967fa.accept_13_2_8_6_1_2390 41 60 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 162 2 20 30 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 60 162 3 13 20 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 60 162 2 19 30 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 162
  (Polychromatic418967fa.accept_13_11_8_6_1_1023 37 60 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 60 162 6 6 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 60 162 (Polychromatic418967fa.accept_11_2_5_8_1_470 35 60 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 162 2 17 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 60 162 3 11 20 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 60 162 2 16 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 31
  60 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 162 6 5 10 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 162
  (Polychromatic418967fa.accept_21_8_18_15_1_5812 29 60 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 60 162 2 14 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 60 162 3 9 20 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 60 162 2 13 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 60 162 (Polychromatic418967fa.accept_11_3_5_8_1_458 25 60 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 162 6 4 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 162 (Polychromatic418967fa.accept_16_7_12_2_1_8902 23 60 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 162 2 11 30 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 60 162 3 7 20 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 60 162 2 10 30 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 162
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 60 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 60 162 6 3 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 60 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 60 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 162 2 8 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 60 162 3 5 20 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 60 162 2 7 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 162 (Polychromatic418967fa.accept_11_2_5_8_1_470 13 60 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 162 6 2 10 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 162
  (Polychromatic418967fa.accept_13_11_8_6_1_1023 11 60 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 60 162 2 5 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 60 162 3 3 20 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 60 162 2 4 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 60 162 (Polychromatic418967fa.accept_16_7_12_2_1_8902 7 60 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 162 6 1 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 60 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 162 2 2 30 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 60 162 3 1 20 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 60 162 2 1 30 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 162
  (Polychromatic418967fa.accept_13_1_8_6_1_1016 1 60 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 60 162)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 162 (allA_succ_of_accept 58
  59 162 (accept_3_4 58 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 162 (Polychromatic418967fa.accept_11_1_4_8_1_1918 56 59 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 162 (accept_3_4 55 59 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 59 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 53
  59 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 162 (accept_3_4 52 59
  162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 162 (Polychromatic418967fa.accept_7_2_3_1_1_10
  51 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 59 162
  (Polychromatic418967fa.accept_17_16_8_9_1_1772 50 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 59 162 (accept_3_4 49 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  59 162 (Polychromatic418967fa.accept_13_9_7_6_1_1673 48 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 59 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 59 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 162 (accept_3_4 46 59 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 59 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 59 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 59 162
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 59 162 (accept_3_4 43 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  59 162 (Polychromatic418967fa.accept_26_16_7_6_1_8941 42 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 59 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 59 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 162 (accept_3_4 40 59 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 59 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 162
  (Polychromatic418967fa.accept_13_12_7_6_1_1015 38 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 59 162 (accept_3_4 37 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  59 162 (Polychromatic418967fa.accept_19_17_2_10_1_8940 36 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 59 162 (Polychromatic418967fa.accept_13_9_7_6_1_1673 35 59 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 162 (accept_3_4 34 59 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 59 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 59 162
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 59 162 (accept_3_4 31 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  59 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 59 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 59 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 162 (accept_3_4 28 59 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 59 162 (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 59 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 162
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 59 162 (accept_3_4 25 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  59 162 (Polychromatic418967fa.accept_15_9_14_12_1_913 24 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 59 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 59 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 162 (accept_3_4 22 59 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 59 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 162
  (Polychromatic418967fa.accept_25_20_9_12_1_8939 20 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 59 162 (accept_3_4 19 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  59 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 59 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 59 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 162 (accept_3_4 16 59 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 162 (Polychromatic418967fa.accept_30_15_29_12_1_8938 15 59 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 162
  (Polychromatic418967fa.accept_13_1_7_6_1_142 14 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 59 162 (accept_3_4 13 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  59 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 59 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 59 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 162 (accept_3_4 10 59 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 59 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 59 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 162
  (Polychromatic418967fa.accept_19_8_2_10_1_7415 8 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 59 162 (accept_3_4 7 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59
  162 (Polychromatic418967fa.accept_16_6_11_2_1_6485 6 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 59 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 59 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 162 (accept_3_4 4 59 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 162 (Polychromatic418967fa.accept_20_3_19_2_1_5926 3 59 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 162
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 59 162 (accept_3_4 1 59 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59
  162))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 162 (allA_succ_of_accept 57 58 162
  (Polychromatic418967fa.accept_12_9_10_6_1_872 57 58 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 58 162 2 28 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 58 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 58 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 58 162 2 27 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 58 162 (accept_3_5 53 58 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58 162 2 26 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 58 162 (Polychromatic418967fa.accept_12_3_10_6_1_442 51 58 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 58 162 2 25 29 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 58 162
  (Polychromatic418967fa.accept_11_5_3_8_1_454 49 58 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 58 162 2 24 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 58 162 (accept_3_5 47 58 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 58
  162 2 23 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  58 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 58 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 58 162 2 22 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 58 162 (Polychromatic418967fa.accept_14_1_2_8_1_655 43 58 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 58 162 2 21 29 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 58 162 (accept_3_5 41 58 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 58 162 2 20 29 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 58 162
  (Polychromatic418967fa.accept_11_6_3_8_1_843 39 58 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 58 162 2 19 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 58 162 (Polychromatic418967fa.accept_20_17_18_2_1_8937 37 58 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 58 162 2 18 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 58 162 (accept_3_5 35 58 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58 162 2 17 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 58 162 (Polychromatic418967fa.accept_12_9_10_6_1_872 33 58 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 58 162 2 16 29 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 58 162
  (Polychromatic418967fa.accept_7_3_2_1_1_225 31 58 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 58 162 2 15 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 58 162 (accept_3_5 29 58 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 58
  162 2 14 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  58 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 58 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 58 162 2 13 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 58 162 (Polychromatic418967fa.accept_10_5_8_2_1_517 25 58 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 58 162 2 12 29 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 58 162 (accept_3_5 23 58 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58 162 2 11 29 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 58 162
  (Polychromatic418967fa.accept_12_9_10_6_1_872 21 58 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 58 162 2 10 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 58 162 (Polychromatic418967fa.accept_17_2_7_9_1_2796 19 58 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 58 162 2 9 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 58 162 (accept_3_5 17 58 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 58 162 2 8 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 58 162 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 58 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 58 162 2 7 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 58 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 13
  58 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 162 2 6 29 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 162 (accept_3_5 11
  58 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 162 2 5 29 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 58 162
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 58 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 58 162 2 4 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 58 162 (Polychromatic418967fa.accept_19_7_1_10_1_4702 7 58 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 162 2 3 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 162 (accept_3_5 5 58 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 58 162 2 2 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 58 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 58 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 162 2 1 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 162 (Polychromatic418967fa.accept_14_1_2_8_1_655 1
  58 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  162)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 162 (allA_succ_of_accept 56 57 162
  (Polychromatic418967fa.accept_12_8_9_6_1_127 56 57 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 57 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 57 162 3 18 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 57 162 (Polychromatic418967fa.accept_13_1_5_6_1_1048
  53 57 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 162
  (Polychromatic418967fa.accept_12_4_9_6_1_440 52 57 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 57 162 3 17 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 57 162 (Polychromatic418967fa.accept_12_2_9_6_1_439 50 57 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 162 (Polychromatic418967fa.accept_10_9_7_2_1_887 49 57 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 57 162 3 16 19 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 57 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 57 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 57 162 (Polychromatic418967fa.accept_12_10_9_6_1_1445 46 57 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 57 162 3 15 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 57 162 (Polychromatic418967fa.accept_10_4_7_2_1_211 44
  57 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 57 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 57 162 3 14 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 57 162 (Polychromatic418967fa.accept_25_16_7_12_1_8936 41 57 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 162 (Polychromatic418967fa.accept_12_4_9_6_1_440 40 57 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 162 3 13 19 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 162
  (Polychromatic418967fa.accept_11_5_2_8_1_866 38 57 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 162 (Polychromatic418967fa.accept_13_11_5_6_1_519 37 57 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 162 3 12 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 35
  57 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 162
  (Polychromatic418967fa.accept_10_4_7_2_1_211 34 57 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 57 162 3 11 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 57 162 (Polychromatic418967fa.accept_12_8_9_6_1_127 32 57 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 57 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 162 3 10 19 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 162
  (Polychromatic418967fa.accept_10_9_7_2_1_887 29 57 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 162 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 57 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 162 3 9 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 162 (Polychromatic418967fa.accept_12_2_9_6_1_439 26 57 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 162
  (Polychromatic418967fa.accept_10_5_7_2_1_516 25 57 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 57 162 3 8 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 57 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 57 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 162 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 57
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 162 3 7 19 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 162
  (Polychromatic418967fa.accept_12_8_9_6_1_127 20 57 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 57 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 162 3 6 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 162 (Polychromatic418967fa.accept_13_4_5_6_1_3201 17 57 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 162
  (Polychromatic418967fa.accept_11_5_2_8_1_866 16 57 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 57 162 3 5 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 57 162 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 57 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 162 (Polychromatic418967fa.accept_23_13_11_1_1_7158 13 57
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 162 3 4 19 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 57 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 162 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 57 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 162 3 3 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 162 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 57 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 57 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 57 162 3 2 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 57 162 (Polychromatic418967fa.accept_10_5_7_2_1_516 5 57 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 162 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 57 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 162 3 1 19 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 162
  (Polychromatic418967fa.accept_12_2_9_6_1_439 2 57 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 162 (Polychromatic418967fa.accept_13_1_5_6_1_1048 1 57 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 57 162))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  56 162 (allA_succ_of_accept 55 56 162 (accept_3_4 55 56 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  54 56 162 2 27 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 56 162 (Polychromatic418967fa.accept_15_8_11_12_1_1626 53 56 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 162 2 26 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 51
  56 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 56 162 2 25 28 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 56 162 (accept_3_4 49
  56 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 56 162 2 24 28 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 56 162
  (Polychromatic418967fa.accept_17_13_5_9_1_1762 47 56 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 56 162 2 23 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 56 162 (Polychromatic418967fa.accept_12_9_8_6_1_466 45 56 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 56 162 2 22 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 56 162 (accept_3_4 43 56 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 162 2 21 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 56 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 41 56 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 56 162 2 20 28 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 56 162
  (Polychromatic418967fa.accept_12_3_8_6_1_895 39 56 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 56 162 2 19 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 56 162 (accept_3_4 37 56 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56
  162 2 18 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  56 162 (Polychromatic418967fa.accept_13_9_4_6_1_1005 35 56 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 56 162 2 17 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 56 162 (Polychromatic418967fa.accept_12_9_8_6_1_466 33 56 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 56 162 2 16 28 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 56 162 (accept_3_4 31 56 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56 162 2 15 28 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 56 162
  (Polychromatic418967fa.accept_15_14_11_12_1_4440 29 56 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 56 162 2 14 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 56 162 (Polychromatic418967fa.accept_12_3_8_6_1_895 27 56 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 162 2 13 28 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 162 (accept_3_4 25 56 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 162 2 12 28 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 56 162
  (Polychromatic418967fa.accept_13_10_4_6_1_3224 23 56 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 56 162 2 11 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 56 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 56 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 56 162 2 10 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 56 162 (accept_3_4 19 56 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56 162 2 9 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 56 162 (Polychromatic418967fa.accept_19_17_18_10_1_7485 17 56 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 56 162 2 8 28 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 56 162
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 56 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 56 162 2 7 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 56 162 (accept_3_4 13 56 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56
  162 2 6 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  56 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 56 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 56 162 2 5 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 56 162 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 56 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 56 162 2 4 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 56 162 (accept_3_4 7 56 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 162 2 3 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 56 162 (Polychromatic418967fa.accept_13_5_4_6_1_2371 5 56 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 56 162 2 2 28 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 56 162
  (Polychromatic418967fa.accept_12_3_8_6_1_895 3 56 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 56 162 2 1 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 56 162 (accept_3_4 1 56 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56
  162)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 162 (allA_succ_of_accept 54 55 162
  (Polychromatic418967fa.accept_7_5_6_1_1_407 54 55 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 55 162 (accept_3_5 53 55 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  55 162 (Polychromatic418967fa.accept_15_7_10_12_1_2403 52 55 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 55 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 55 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 162 (accept_3_5 50 55 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 55 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 55 162
  (Polychromatic418967fa.accept_10_8_5_2_1_881 48 55 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 55 162 (accept_3_5 47 55 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  55 162 (Polychromatic418967fa.accept_17_12_4_9_1_3889 46 55 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 55 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 55 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 162 (accept_3_5 44 55 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 162 (Polychromatic418967fa.accept_10_3_5_2_1_38 43 55 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 162
  (Polychromatic418967fa.accept_19_4_17_10_1_4632 42 55 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 162 (accept_3_5 41 55 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  55 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 55 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 55 162 (Polychromatic418967fa.accept_15_9_10_12_1_1625 39 55 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 162 (accept_3_5 38 55 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 55 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 162
  (Polychromatic418967fa.accept_13_10_3_6_1_1003 36 55 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 162 (accept_3_5 35 55 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 162 (Polychromatic418967fa.accept_19_15_17_10_1_8935 34 55 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 55 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 55 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 162 (accept_3_5 32 55 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 162 (Polychromatic418967fa.accept_13_5_3_6_1_3278 31 55 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 162
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 55 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 162 (accept_3_5 29 55 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 162 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 55 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 162 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 55 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 162 (accept_3_5 26 55 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 55 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 162
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 24 55 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 162 (accept_3_5 23 55 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 162 (Polychromatic418967fa.accept_13_9_3_6_1_1661 22 55 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 55 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 162 (accept_3_5 20 55 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 55 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 162
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 55 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 162 (accept_3_5 17 55 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 55 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 162 (Polychromatic418967fa.accept_19_15_17_10_1_8935 15 55 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 162 (accept_3_5 14 55 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 55 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 162
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 55 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 162 (accept_3_5 11 55 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 162 (Polychromatic418967fa.accept_13_10_3_6_1_1003 10 55 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 55 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 162 (accept_3_5 8 55 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 162 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 55 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 162
  (Polychromatic418967fa.accept_15_6_10_12_1_2538 6 55 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 162 (accept_3_5 5 55 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  162 (Polychromatic418967fa.accept_19_4_17_10_1_4632 4 55 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 55 162 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 55 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 162 (accept_3_5 2 55 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 55 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  162))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 162 (allA_succ_of_accept 53 54 162
  (Polychromatic418967fa.accept_7_4_5_1_1_418 53 54 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 162 2 26 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 51 54 162 3 17 18 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 54 162 2 25 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 54 162 (Polychromatic418967fa.accept_13_10_2_6_1_1044 49 54 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 162 6 8 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 162 (Polychromatic418967fa.accept_10_7_4_2_1_903 47 54 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 162 2 23 27 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 54 162 9 5 6 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 54 162 2 22 27 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 162
  (Polychromatic418967fa.accept_13_4_2_6_1_1043 43 54 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 162 6 7 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 54 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 54 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54 162 2 20 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 54 162 3 13 18 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 54 162 2 19 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 162 (Polychromatic418967fa.accept_10_7_4_2_1_903 37
  54 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 162 18 2 3 9 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 162
  (Polychromatic418967fa.accept_13_9_2_6_1_514 35 54 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 54 162 2 17 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 54 162 3 11 18 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 54 162 2 16 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 54 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 54 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 162 6 5 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 162 (Polychromatic418967fa.accept_15_14_9_12_1_2498 29 54
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 162 2 14 27 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 54 162 27 1 2 6 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 54 162 2 13 27 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 162
  (Polychromatic418967fa.accept_7_4_5_1_1_418 25 54 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 162 6 4 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 54 162 (Polychromatic418967fa.accept_13_10_2_6_1_1044 23 54 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 162 2 11 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 54 162 3 7 18 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 54 162 2 10 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 162 (Polychromatic418967fa.accept_15_4_9_12_1_2495
  19 54 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 162 18 1 3 9 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 162
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 54 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 54 162 2 8 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 54 162 3 5 18 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 54 162 2 7 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 54 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 54 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 162 6 2 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 54 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 162 2 5 27 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 54 162 9 1 6 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 54 162 2 4 27 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 162
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 54 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 54 162 6 1 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 54 162 (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 54 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 162 2 2 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 54 162 3 1 18 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 54 162 2 1 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 162 (Polychromatic418967fa.accept_13_1_2_6_1_515 1 54 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  162)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 162 (allA_succ_of_accept 52 53 162 (accept_3_4
  52 53 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 53 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 162 (Polychromatic418967fa.accept_15_5_8_12_1_2435 50 53 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 162 (accept_3_4 49 53 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 162 (Polychromatic418967fa.accept_13_9_1_6_1_510 48 53 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  53 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 162 (accept_3_4 46 53
  162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 162 (Polychromatic418967fa.accept_7_3_4_1_1_71
  45 53 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 53 162
  (Polychromatic418967fa.accept_13_5_1_6_1_2367 44 53 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 53 162 (accept_3_4 43 53 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  53 162 (Polychromatic418967fa.accept_13_3_1_6_1_509 42 53 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 53 162 (Polychromatic418967fa.accept_10_1_3_2_1_220 41 53 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 162 (accept_3_4 40 53 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 53 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 53 162
  (Polychromatic418967fa.accept_7_3_4_1_1_71 38 53 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 53 162 (accept_3_4 37 53 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  53 162 (Polychromatic418967fa.accept_19_17_15_10_1_8934 36 53 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 53 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 53 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 162 (accept_3_4 34 53 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 53 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 162
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 32 53 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 53 162 (accept_3_4 31 53 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  53 162 (Polychromatic418967fa.accept_19_11_15_10_1_7406 30 53 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 53 162 (Polychromatic418967fa.accept_13_3_1_6_1_509 29 53 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 162 (accept_3_4 28 53 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 53 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 162
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 53 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 53 162 (accept_3_4 25 53 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  53 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 53 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 53 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 53 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 162 (accept_3_4 22 53 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 162 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 53 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 162
  (Polychromatic418967fa.accept_13_7_1_6_1_3287 20 53 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 53 162 (accept_3_4 19 53 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  53 162 (Polychromatic418967fa.accept_13_5_1_6_1_2367 18 53 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 53 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 53 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 162 (accept_3_4 16 53 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 53 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 162
  (Polychromatic418967fa.accept_19_14_15_10_1_3359 14 53 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 53 162 (accept_3_4 13 53 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 53 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 53 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 53 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 162 (accept_3_4 10 53 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 162 (Polychromatic418967fa.accept_13_9_1_6_1_510 9
  53 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 162
  (Polychromatic418967fa.accept_13_8_1_6_1_997 8 53 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 162 (accept_3_4 7 53 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53
  162 (Polychromatic418967fa.accept_19_6_15_10_1_2170 6 53 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 53 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 53 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 162 (accept_3_4 4 53 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 53 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 53 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 162
  (Polychromatic418967fa.accept_13_2_1_6_1_2365 2 53 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 53 162 (accept_3_4 1 53 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53
  162))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 162 (allA_succ_of_accept 51 52 162
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 52 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 52 162 2 25 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 52 162 (Polychromatic418967fa.accept_15_4_7_12_1_5538 49 52 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 52 162 2 24 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 52 162 (accept_3_5 47 52 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52 162 2 23 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 52 162 (Polychromatic418967fa.accept_12_9_4_6_1_460 45 52 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 52 162 2 22 26 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 52 162
  (Polychromatic418967fa.accept_19_5_14_10_1_8933 43 52 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 52 162 2 21 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 52 162 (accept_3_5 41 52 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52
  162 2 20 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  52 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 52 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 52 162 2 19 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 52 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 52 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 52 162 2 18 26 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 52 162 (accept_3_5 35 52 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52 162 2 17 26 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 52 162
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 52 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 52 162 2 16 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 52 162 (Polychromatic418967fa.accept_19_12_14_10_1_4625 31 52 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 52 162 2 15 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 52 162 (accept_3_5 29 52 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52 162 2 14 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 52 162 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 52 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 52 162 2 13 26 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 52 162
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 52 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 52 162 2 12 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 52 162 (accept_3_5 23 52 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52
  162 2 11 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  52 162 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 52 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 52 162 2 10 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 52 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 52 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 52 162 2 9 26 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 52 162 (accept_3_5 17 52 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52 162 2 8 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 52 162 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 52 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 52 162 2 7 26 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 52 162
  (Polychromatic418967fa.accept_29_13_23_17_1_8932 13 52 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 52 162 2 6 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 52 162 (accept_3_5 11 52 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 52 162 2 5 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 52 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 52 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 52 162 2 4 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 52 162 (Polychromatic418967fa.accept_19_7_14_10_1_6034 7 52 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 162 2 3 26 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 162 (accept_3_5 5 52 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 162 2 2 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 52 162 (Polychromatic418967fa.accept_12_3_4_6_1_434 3
  52 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 52 162 2 1 26 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 52 162
  (Polychromatic418967fa.accept_19_1_14_10_1_4619 1 52 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 52 162)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 162 (allA_succ_of_accept 50 51 162
  (Polychromatic418967fa.accept_12_2_3_6_1_112 50 51 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 51 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 51 162 3 16 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 51 162 (Polychromatic418967fa.accept_15_2_6_12_1_1613
  47 51 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 162
  (Polychromatic418967fa.accept_10_6_1_2_1_874 46 51 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 51 162 3 15 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 51 162 (Polychromatic418967fa.accept_12_8_3_6_1_909 44 51 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 162 (Polychromatic418967fa.accept_10_3_1_2_1_521 43 51 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 162 3 14 17 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 51 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 51 162 (Polychromatic418967fa.accept_12_4_3_6_1_879 40 51 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 51 162 3 13 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 51 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 38
  51 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 37 51 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 51 162 3 12 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 51 162 (Polychromatic418967fa.accept_15_5_6_12_1_916 35 51 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 51 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 162 3 11 17 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 162
  (Polychromatic418967fa.accept_12_8_3_6_1_909 32 51 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 51 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 51 162 3 10 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 51 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 51
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 162
  (Polychromatic418967fa.accept_12_4_3_6_1_879 28 51 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 51 162 3 9 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 51 162 (Polychromatic418967fa.accept_10_6_1_2_1_874 26 51 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 51 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 162 3 8 17 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 162
  (Polychromatic418967fa.accept_10_3_1_2_1_521 23 51 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 162 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 51 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 162 3 7 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 51 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 162
  (Polychromatic418967fa.accept_10_9_1_2_1_522 19 51 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 51 162 3 6 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 51 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 51 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 162 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 51 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 162 3 5 17 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 162
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 51 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 51 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 162 3 4 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 162 (Polychromatic418967fa.accept_21_11_9_15_1_5746 11 51
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 162
  (Polychromatic418967fa.accept_7_3_2_1_1_225 10 51 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 51 162 3 3 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 51 162 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 51 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 162 (Polychromatic418967fa.accept_13_7_12_6_1_1039 7 51 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 162 3 2 17 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 51 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 162 (Polychromatic418967fa.accept_11_4_7_8_1_1926 4 51 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 162 3 1 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 162 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 51 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 51 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 51 162))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 162 (allA_succ_of_accept 49 50 162
  (accept_3_4 49 50 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 50 162 2 24 25 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 50 162
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 47 50 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 50 162 2 23 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 50 162 (Polychromatic418967fa.accept_12_9_2_6_1_455 45 50 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 50 162 2 22 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 162 (accept_3_4 43 50 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 162 2 21 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 162 (Polychromatic418967fa.accept_19_3_12_10_1_6015 41 50
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 50 162 2 20 25 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 50 162
  (Polychromatic418967fa.accept_12_3_2_6_1_138 39 50 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 50 162 2 19 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 50 162 (accept_3_4 37 50 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50
  162 2 18 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  50 162 (Polychromatic418967fa.accept_20_15_10_2_1_5924 35 50 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 50 162 2 17 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 50 162 (Polychromatic418967fa.accept_12_9_2_6_1_455 33 50 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 50 162 2 16 25 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 50 162 (accept_3_4 31 50 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50 162 2 15 25 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 50 162
  (Polychromatic418967fa.accept_31_29_19_7_1_8931 29 50 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 50 162 2 14 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 50 162 (Polychromatic418967fa.accept_12_3_2_6_1_138 27 50 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 162 2 13 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 50 162 (accept_3_4 25 50 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 50 162 2 12 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 162 (Polychromatic418967fa.accept_15_8_5_12_1_4453 23 50 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 50 162 2 11 25 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 50 162
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 50 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 50 162 2 10 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 50 162 (accept_3_4 19 50 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50
  162 2 9 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  50 162 (Polychromatic418967fa.accept_13_4_11_6_1_1033 17 50 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 50 162 2 8 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 50 162 (Polychromatic418967fa.accept_12_3_2_6_1_138 15 50 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 50 162 2 7 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 50 162 (accept_3_4 13 50 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50 162 2 6 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 50 162 (Polychromatic418967fa.accept_19_11_12_10_1_7480 11 50 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 50 162 2 5 25 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 50 162
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 50 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 50 162 2 4 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 50 162 (accept_3_4 7 50 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 162
  2 3 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 50
  162 (Polychromatic418967fa.accept_13_5_11_6_1_505 5 50 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 50 162 2 2 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 50 162 (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 50 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 162 2 1 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 162 (accept_3_4 1 50 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 50 162)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 162
  (allA_succ_of_accept 48 49 162 (Polychromatic418967fa.accept_13_9_10_6_1_1028 48 49 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 162 (accept_3_5 47 49 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 49 162 (Polychromatic418967fa.accept_11_2_5_8_1_470 46 49 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 162 (Polychromatic418967fa.accept_21_3_7_15_1_4300
  45 49 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 162 (accept_3_5 44
  49 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 49 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 49 162 (Polychromatic418967fa.accept_13_3_10_6_1_2382 42 49 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 162 (accept_3_5 41 49 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 49 162 (Polychromatic418967fa.accept_17_6_15_9_1_1791 40 49 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 49 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 162 (accept_3_5 38 49 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 162 (Polychromatic418967fa.accept_10_7_9_2_1_1887 37 49 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 162 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 49 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 162 (accept_3_5 35 49 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 162 (Polychromatic418967fa.accept_14_6_7_8_1_624 34 49 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 162
  (Polychromatic418967fa.accept_20_13_9_2_1_5933 33 49 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 162 (accept_3_5 32 49 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 49 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 162 (Polychromatic418967fa.accept_13_4_10_6_1_989 30 49 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 162 (accept_3_5 29 49 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 162 (Polychromatic418967fa.accept_13_2_10_6_1_1676 28 49 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 49 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 162 (accept_3_5 26 49 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 162 (Polychromatic418967fa.accept_11_3_5_8_1_458 25 49 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 162 (Polychromatic418967fa.accept_11_2_5_8_1_470 24 49 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 162 (accept_3_5 23 49 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 162 (Polychromatic418967fa.accept_13_9_10_6_1_1028 22 49 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 162
  (Polychromatic418967fa.accept_10_1_9_2_1_45 21 49 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 162 (accept_3_5 20 49 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 49 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 162 (Polychromatic418967fa.accept_13_5_10_6_1_2361 18 49 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 162 (accept_3_5 17 49 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 162 (Polychromatic418967fa.accept_13_3_10_6_1_2382 16 49
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 49 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 162 (accept_3_5 14 49 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 162 (Polychromatic418967fa.accept_11_2_5_8_1_470 13 49 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 162 (Polychromatic418967fa.accept_13_12_10_6_1_3212 12 49 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 162 (accept_3_5 11 49 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 162 (Polychromatic418967fa.accept_21_10_7_15_1_8930 10 49
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 162
  (Polychromatic418967fa.accept_13_9_10_6_1_1028 9 49 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 162 (accept_3_5 8 49 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  162 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 49 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 49 162 (Polychromatic418967fa.accept_14_6_7_8_1_624 6 49 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 162 (accept_3_5 5 49 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 162 (Polychromatic418967fa.accept_13_4_10_6_1_989 4 49 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 49
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 162 (accept_3_5 2 49 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 162 (Polychromatic418967fa.accept_10_1_9_2_1_45 1
  49 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49
  162))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 162 (allA_succ_of_accept 47 48 162
  (Polychromatic418967fa.accept_7_5_6_1_1_407 47 48 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 48 162 2 23 24 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 48 162 3 15 16 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 48 162 2 22 24 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 48 162 (Polychromatic418967fa.accept_13_4_9_6_1_2376 43 48 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 162 6 7 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 162 (Polychromatic418967fa.accept_13_2_9_6_1_501 41 48 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 162 2 20 24 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 48 162 3 13 16 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 48 162 2 19 24 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 162
  (Polychromatic418967fa.accept_7_2_6_1_1_73 37 48 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 162 6 6 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 48 162 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 48 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 162 2 17 24 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 48 162 3 11 16 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 48 162 2 16 24 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 162 (Polychromatic418967fa.accept_21_10_6_15_1_8929
  31 48 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 162 6 5 8 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 162
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 29 48 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 48 162 2 14 24 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 48 162 3 9 16 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 48 162 2 13 24 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 48 162 (Polychromatic418967fa.accept_10_5_8_2_1_517 25 48 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 162 6 4 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 48 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 162 2 11 24 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 48 162 3 7 16 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 48 162 2 10 24 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 162
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 48 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 48 162 6 3 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 48 162 (Polychromatic418967fa.accept_13_4_9_6_1_2376 17 48 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 162 2 8 24 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 48 162 3 5 16 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 48 162 2 7 24 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 162 (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 48
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 162 6 2 8 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 162
  (Polychromatic418967fa.accept_21_11_6_15_1_5764 11 48 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 48 162 2 5 24 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 48 162 3 3 16 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 48 162 2 4 24 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 162 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 48 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 162 6 1 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 48 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 162 2 2 24 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 48 162 3 1 16 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 48 162 2 1 24 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 162
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 1 48 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 48 162)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 162 (allA_succ_of_accept 46 47 162
  (accept_3_4 46 47 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 47 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 162 (Polychromatic418967fa.accept_10_4_7_2_1_211 44 47 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 162 (accept_3_4 43 47 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 162 (Polychromatic418967fa.accept_19_4_9_10_1_8928 42 47 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 47 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 162 (accept_3_4 40 47 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 47 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 38 47 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 162 (accept_3_4 37 47 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 162 (Polychromatic418967fa.accept_15_6_2_12_1_885 36 47 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 162
  (Polychromatic418967fa.accept_10_5_7_2_1_516 35 47 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 162 (accept_3_4 34 47 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 47 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 47 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 162 (accept_3_4 31 47 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 162 (Polychromatic418967fa.accept_21_9_5_15_1_5741 30 47 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 47 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 162 (accept_3_4 28 47 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 47 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 162 (Polychromatic418967fa.accept_19_7_9_10_1_4600 26 47 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 162 (accept_3_4 25 47 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 47 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 162
  (Polychromatic418967fa.accept_19_4_9_10_1_8928 23 47 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 162 (accept_3_4 22 47 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 47 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 47 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 162 (accept_3_4 19 47 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 47 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 47 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 162 (accept_3_4 16 47 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 162 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 47 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 162 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 47 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 162 (accept_3_4 13 47 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 162 (Polychromatic418967fa.accept_16_12_15_2_1_6473 12 47 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 162
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 47 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 162 (accept_3_4 10 47 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 47 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 47 162 (Polychromatic418967fa.accept_21_8_5_15_1_4208 8 47 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 162 (accept_3_4 7 47 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 47 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 47 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 47
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 162 (accept_3_4 4 47 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 47
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 162
  (Polychromatic418967fa.accept_13_2_8_6_1_2390 2 47 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 47 162 (accept_3_4 1 47 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47
  162))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 162 (allA_succ_of_accept 45 46 162
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 46 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 46 162 2 22 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 46 162 (Polychromatic418967fa.accept_13_4_7_6_1_2359 43 46 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 162 2 21 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 162 (accept_3_5 41 46 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 162 2 20 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 162 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 46 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 46 162 2 19 23 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 46 162
  (Polychromatic418967fa.accept_19_18_8_10_1_7489 37 46 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 46 162 2 18 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 46 162 (accept_3_5 35 46 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46
  162 2 17 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  46 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 46 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 46 162 2 16 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 46 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 46 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 46 162 2 15 23 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 46 162 (accept_3_5 29 46 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 46 162 2 14 23 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 46 162
  (Polychromatic418967fa.accept_11_5_2_8_1_866 27 46 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 46 162 2 13 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 46 162 (Polychromatic418967fa.accept_13_12_7_6_1_1015 25 46 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 162 2 12 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 162 (accept_3_5 23 46 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 162 2 11 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 46 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 46 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 46 162 2 10 23 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 46 162
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 46 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 46 162 2 9 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 46 162 (accept_3_5 17 46 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46
  162 2 8 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  46 162 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 46 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 46 162 2 7 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 46 162 (Polychromatic418967fa.accept_15_13_1_12_1_1638 13 46 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 162 2 6 23 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 162 (accept_3_5 11 46 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 162 2 5 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 46 162 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 46 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 46 162 2 4 23 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 46 162
  (Polychromatic418967fa.accept_35_7_11_22_1_8927 7 46 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 46 162 2 3 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 46 162 (accept_3_5 5 46 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 46 162
  2 2 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 46
  162 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 46 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 46 162 2 1 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 46 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 46 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 46 162)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 162
  (allA_succ_of_accept 44 45 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 45 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 45 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 162 3 14 15 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 162
  (Polychromatic418967fa.accept_19_3_7_10_1_6023 41 45 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 45 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 45 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 45 162 3 13 15 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 45 162 (Polychromatic418967fa.accept_10_8_5_2_1_881 38
  45 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 162
  (Polychromatic418967fa.accept_7_2_3_1_1_10 37 45 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 45 162 9 4 5 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 45 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 45 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 162 (Polychromatic418967fa.accept_12_10_9_6_1_1445 34 45
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 162 3 11 15 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 162
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 45 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 45 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 162 3 10 15 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 162 (Polychromatic418967fa.accept_21_8_3_15_1_2875
  29 45 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 162
  (Polychromatic418967fa.accept_10_8_5_2_1_881 28 45 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 45 162 9 3 5 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 45 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 45 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 45 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 162 3 8 15 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 45 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 45 162 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 45 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 45 162 3 7 15 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 45 162 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 45 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 45 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 45 162 9 2 5 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 45 162 (Polychromatic418967fa.accept_10_7_5_2_1_880 17 45 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 45 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 162 3 5 15 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 162
  (Polychromatic418967fa.accept_12_2_9_6_1_439 14 45 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 162 (Polychromatic418967fa.accept_10_3_5_2_1_38 13 45 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 45 162 3 4 15 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 45 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 45 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 162
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 45 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 45 162 9 1 5 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 45 162 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 45 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 45 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 162 3 2 15 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 162
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 45 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 45 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 45 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 45 162 3 1 15 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 45 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 45 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 162
  (Polychromatic418967fa.accept_19_1_7_10_1_8926 1 45 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 45 162))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 162 (allA_succ_of_accept 43 44 162
  (accept_3_4 43 44 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 44 162 2 21 22 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 44 162
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 44 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 44 162 2 20 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 44 162 (Polychromatic418967fa.accept_12_3_8_6_1_895 39 44 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 162 2 19 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 162 (accept_3_4 37 44 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 162 2 18 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 162 (Polychromatic418967fa.accept_17_1_10_9_1_3884 35 44 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 162 2 17 22 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 44 162
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 44 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 44 162 2 16 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 44 162 (accept_3_4 31 44 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44
  162 2 15 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  44 162 (Polychromatic418967fa.accept_13_3_5_6_1_3192 29 44 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 44 162 2 14 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 44 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 44 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 44 162 2 13 22 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 44 162 (accept_3_4 25 44 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44 162 2 12 22 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 44 162
  (Polychromatic418967fa.accept_13_10_5_6_1_1671 23 44 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 44 162 2 11 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 44 162 (Polychromatic418967fa.accept_12_9_8_6_1_466 21 44 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 162 2 10 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 162 (accept_3_4 19 44 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44 162 2 9 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 44 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 44 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 44 162 2 8 22 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 44 162
  (Polychromatic418967fa.accept_12_3_8_6_1_895 15 44 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 44 162 2 7 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 44 162 (accept_3_4 13 44 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44
  162 2 6 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  44 162 (Polychromatic418967fa.accept_13_11_5_6_1_519 11 44 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 44 162 2 5 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 44 162 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 44 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 162 2 4 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 162 (accept_3_4 7 44 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 162 2 3 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 44 162 (Polychromatic418967fa.accept_20_5_4_2_1_5912 5 44 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 44 162 2 2 22 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 44 162
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 44 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 44 162 2 1 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 44 162 (accept_3_4 1 44 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44
  162)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 162 (allA_succ_of_accept 42 43 162
  (Polychromatic418967fa.accept_11_9_10_8_1_444 42 43 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 162 (accept_3_5 41 43 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 162 (Polychromatic418967fa.accept_15_10_13_12_1_3384 40 43 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 162 (Polychromatic418967fa.accept_16_7_11_2_1_3117 39 43 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 162 (accept_3_5 38 43 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 43 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 162
  (Polychromatic418967fa.accept_13_10_4_6_1_3224 36 43 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 162 (accept_3_5 35 43 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 162 (Polychromatic418967fa.accept_19_15_5_10_1_8925 34 43 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 43 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 162 (accept_3_5 32 43 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 162 (Polychromatic418967fa.accept_10_1_3_2_1_220 31 43 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 162
  (Polychromatic418967fa.accept_14_2_1_8_1_650 30 43 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 162 (accept_3_5 29 43 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 162 (Polychromatic418967fa.accept_13_2_4_6_1_2356 28 43 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 162 (Polychromatic418967fa.accept_19_8_5_10_1_7373 27 43 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 162 (accept_3_5 26 43 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 43 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 162
  (Polychromatic418967fa.accept_13_11_4_6_1_1006 24 43 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 162 (accept_3_5 23 43 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 162 (Polychromatic418967fa.accept_13_9_4_6_1_1005 22 43 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 43 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 162 (accept_3_5 20 43 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 162 (Polychromatic418967fa.accept_20_19_3_2_1_3118 19 43 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 162
  (Polychromatic418967fa.accept_13_5_4_6_1_2371 18 43 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 162 (accept_3_5 17 43 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 162 (Polychromatic418967fa.accept_14_2_1_8_1_650 16 43 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 162 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 43 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 162 (accept_3_5 14 43 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 43 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 162
  (Polychromatic418967fa.accept_21_12_1_15_1_8924 12 43 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 162 (accept_3_5 11 43 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 162 (Polychromatic418967fa.accept_13_10_4_6_1_3224 10 43 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 43 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 162 (accept_3_5 8 43 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 162 (Polychromatic418967fa.accept_13_7_4_6_1_3221 7 43 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 162
  (Polychromatic418967fa.accept_16_6_11_2_1_6485 6 43 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 162 (accept_3_5 5 43 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  162 (Polychromatic418967fa.accept_22_4_21_8_1_8923 4 43 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 43 162 (Polychromatic418967fa.accept_15_3_13_12_1_348 3 43 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 162 (accept_3_5 2 43 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 43 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 162)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 42 162 (allA_succ_of_accept 41 42 162 (Polychromatic418967fa.accept_22_19_20_8_1_8920 41 42 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 162 2 20 21 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 42 162 3 13 14 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 42 162 2 19 21 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 162
  (Polychromatic418967fa.accept_28_9_14_22_1_8922 37 42 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 42 162 6 6 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 42 162 (Polychromatic418967fa.accept_13_9_3_6_1_1661 35 42 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 162 2 17 21 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 42 162 3 11 14 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 42 162 2 16 21 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 162 (Polychromatic418967fa.accept_13_5_3_6_1_3278
  31 42 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 162 6 5 7 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 162
  (Polychromatic418967fa.accept_25_4_17_12_1_8921 29 42 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 42 162 2 14 21 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 42 162 3 9 14 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 42 162 2 13 21 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 42 162 (Polychromatic418967fa.accept_19_6_4_10_1_3342 25 42 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 162 6 4 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 162 (Polychromatic418967fa.accept_13_10_3_6_1_1003 23 42 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 162 2 11 21 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 42 162 3 7 14 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 42 162 2 10 21 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 162
  (Polychromatic418967fa.accept_22_19_20_8_1_8920 19 42 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 162 6 3 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 162 (Polychromatic418967fa.accept_19_17_4_10_1_7371 17 42 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 162 2 8 21 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 42 162 3 5 14 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 42 162 2 7 21 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 162 (Polychromatic418967fa.accept_19_13_4_10_1_7452 13 42
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 162 6 2 7 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 162
  (Polychromatic418967fa.accept_17_11_8_9_1_8919 11 42 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 42 162 2 5 21 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 42 162 3 3 14 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 42 162 2 4 21 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 42 162 (Polychromatic418967fa.accept_25_7_17_12_1_8918 7 42 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 162 6 1 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 162 (Polychromatic418967fa.accept_13_5_3_6_1_3278 5 42 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 162 2 2 21 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 42 162 3 1 14 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 42 162 2 1 21 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 162
  (Polychromatic418967fa.accept_13_1_3_6_1_158 1 42 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 42 162)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 162 (allA_succ_of_accept 40 41 162
  (accept_3_4 40 41 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 41 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 162 (Polychromatic418967fa.accept_13_12_2_6_1_2396 38 41 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 162 (accept_3_4 37 41 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 162 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 41 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 35
  41 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 162 (accept_3_4 34 41
  162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 162
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 41 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 41 162 (Polychromatic418967fa.accept_17_15_7_9_1_1809 32 41 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 162 (accept_3_4 31 41 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 41 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 41 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 162 (Polychromatic418967fa.accept_10_9_1_2_1_522
  29 41 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 162 (accept_3_4 28
  41 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 41 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 41 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 41 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 162 (accept_3_4 25 41 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 41 162 (Polychromatic418967fa.accept_19_5_3_10_1_4641 24 41 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 41 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 162 (accept_3_4 22 41 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 162 (Polychromatic418967fa.accept_13_8_2_6_1_2385 21 41 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 162 (Polychromatic418967fa.accept_19_1_3_10_1_8917 20 41 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 162 (accept_3_4 19 41 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 162 (Polychromatic418967fa.accept_21_18_20_15_1_8916 18 41
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 162
  (Polychromatic418967fa.accept_13_4_2_6_1_1043 17 41 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 162 (accept_3_4 16 41 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 41 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 162 (Polychromatic418967fa.accept_13_1_2_6_1_515 14 41 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 162 (accept_3_4 13 41 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 41 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 41 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 162 (accept_3_4 10 41 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 41 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 162 (Polychromatic418967fa.accept_13_8_2_6_1_2385 8 41 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 162 (accept_3_4 7 41 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 162 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 41 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 162
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 41 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 162 (accept_3_4 4 41 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  162 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 41 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 41 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 162 (accept_3_4 1 41 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 162))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 162 (allA_succ_of_accept 39 40 162
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 40 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 40 162 2 19 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 40 162 (Polychromatic418967fa.accept_11_4_7_8_1_1926 37 40 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 162 2 18 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 40 162 (accept_3_5 35 40 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 40 162 2 17 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 40 162 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 40 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 40 162 2 16 20 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 40 162
  (Polychromatic418967fa.accept_7_3_5_1_1_72 31 40 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 40 162 2 15 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 40 162 (accept_3_5 29 40 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40
  162 2 14 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  40 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 40 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 40 162 2 13 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 40 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 40 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 40 162 2 12 20 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 162 (accept_3_5 23 40 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40 162 2 11 20 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 40 162
  (Polychromatic418967fa.accept_12_9_4_6_1_460 21 40 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 40 162 2 10 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 40 162 (Polychromatic418967fa.accept_22_19_18_8_1_8915 19 40 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 162 2 9 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 162 (accept_3_5 17 40 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 40 162 2 8 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 40 162 (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 40 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 40 162 2 7 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 40 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 13
  40 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 162 2 6 20 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 162 (accept_3_5 11
  40 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 162 2 5 20 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 162
  (Polychromatic418967fa.accept_12_9_4_6_1_460 9 40 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 40 162 2 4 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 40 162 (Polychromatic418967fa.accept_13_7_1_6_1_3287 7 40 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 162 2 3 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 162 (accept_3_5 5 40 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 40 162 2 2 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 40 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 40 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 162 2 1 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 162 (Polychromatic418967fa.accept_21_1_19_15_1_8914
  1 40 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  162)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 162 (allA_succ_of_accept 38 39 162
  (Polychromatic418967fa.accept_7_3_4_1_1_71 38 39 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 39 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 162 3 12 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 162 (Polychromatic418967fa.accept_15_5_9_12_1_1599
  35 39 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 162
  (Polychromatic418967fa.accept_12_10_3_6_1_882 34 39 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 162 3 11 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 162 (Polychromatic418967fa.accept_12_8_3_6_1_909 32 39 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 39 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 162 3 10 13 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 39 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 162 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 39 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 162 3 9 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 39 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 39 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 162 3 8 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 162 (Polychromatic418967fa.accept_19_4_1_10_1_7447 23 39 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 162 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 39 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 162 3 7 13 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 162
  (Polychromatic418967fa.accept_12_8_3_6_1_909 20 39 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 39 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 162 3 6 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 39 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 162
  (Polychromatic418967fa.accept_12_4_3_6_1_879 16 39 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 162 3 5 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 162 (Polychromatic418967fa.accept_11_3_6_8_1_1924 14 39 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 39 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 162 3 4 13 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 162
  (Polychromatic418967fa.accept_10_1_9_2_1_45 11 39 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 39 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 162 3 3 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 162 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 39 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 162
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 39 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 162 3 2 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 39 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 162 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 39 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 162 3 1 13 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 162
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 39 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 39 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 162))))))))))))))))))))))))))))))))))))))) (allB_succ 38 162
  (allA_succ_of_accept 37 38 162 (accept_3_4 37 38 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  162 2 18 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  38 162 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 38 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 162 2 17 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 38 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 162 2 16 19 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 162 (accept_3_4 31 38 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 162 2 15 19 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 162
  (Polychromatic418967fa.accept_17_12_4_9_1_3889 29 38 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 162 2 14 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 38 162 (Polychromatic418967fa.accept_12_3_2_6_1_138 27 38 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 162 2 13 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 162 (accept_3_4 25 38 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 162 2 12 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 38 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 162 2 11 19 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 162
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 38 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 162 2 10 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 38 162 (accept_3_4 19 38 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38
  162 2 9 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  38 162 (Polychromatic418967fa.accept_16_1_6_2_1_3100 17 38 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 38 162 2 8 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 38 162 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 38 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 162 2 7 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 162 (accept_3_4 13 38 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 162 2 6 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 38 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 38 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 38 162 2 5 19 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 38 162
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 38 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 38 162 2 4 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 38 162 (accept_3_4 7 38 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 162
  2 3 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38
  162 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 38 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 38 162 2 2 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 38 162 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 38 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 162 2 1 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 162 (accept_3_4 1 38 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 38 162)))))))))))))))))))))))))))))))))))))) (allB_succ 37 162 (allA_succ_of_accept 36 37 162
  (Polychromatic418967fa.accept_15_6_7_12_1_869 36 37 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 162 (accept_3_5 35 37 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 37 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 162 (Polychromatic418967fa.accept_15_3_7_12_1_372 33 37 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 162 (accept_3_5 32 37 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 37 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 162
  (Polychromatic418967fa.accept_13_4_11_6_1_1033 30 37 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 162 (accept_3_5 29 37 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 162 (Polychromatic418967fa.accept_17_11_3_9_1_6387 28 37 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 37 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 162 (accept_3_5 26 37 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 162 (Polychromatic418967fa.accept_10_5_7_2_1_516 25 37 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 162
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 37 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 162 (accept_3_5 23 37 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 162 (Polychromatic418967fa.accept_21_1_16_15_1_8913 22 37 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 162 (Polychromatic418967fa.accept_13_8_11_6_1_1035 21 37 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 162 (accept_3_5 20 37 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 37 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 162
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 37 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 162 (accept_3_5 17 37 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 162 (Polychromatic418967fa.accept_28_16_9_22_1_8912 16 37 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 37 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 162 (accept_3_5 14 37 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 37 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 162
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 37 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 162 (accept_3_5 11 37 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 37 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 162 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 37 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 162 (accept_3_5 8 37 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 37 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 162
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 37 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 162 (accept_3_5 5 37 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  162 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 37 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 37 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 162 (accept_3_5 2 37 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 162 (Polychromatic418967fa.accept_11_1_4_8_1_1918 1 37 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 162))))))))))))))))))))))))))))))))))))) (allB_succ 36 162
  (allA_succ_of_accept 35 36 162 (Polychromatic418967fa.accept_13_9_10_6_1_1028 35 36 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 162 2 17 18 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 36 162 3 11 12 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 36 162 2 16 18 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 31
  36 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 162 6 5 6 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 162
  (Polychromatic418967fa.accept_13_3_10_6_1_2382 29 36 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 36 162 2 14 18 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 36 162 9 3 4 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 36 162 2 13 18 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 162 (Polychromatic418967fa.accept_13_12_10_6_1_3212 25 36 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 162 6 4 6 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 162 (Polychromatic418967fa.accept_19_4_17_10_1_4632 23 36
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 162 2 11 18 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 36 162 3 7 12 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 36 162 2 10 18 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 162
  (Polychromatic418967fa.accept_24_19_12_18_1_8911 19 36 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 36 162 18 1 2 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 36 162 (Polychromatic418967fa.accept_11_6_3_8_1_843 17 36 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 162 2 8 18 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 36 162 3 5 12 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 36 162 2 7 18 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 162
  (Polychromatic418967fa.accept_24_13_12_18_1_8910 13 36 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 36 162 6 2 6 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 36 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 36 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 162 2 5 18 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 36 162 9 1 4 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 36 162 2 4 18 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 162 (Polychromatic418967fa.accept_15_7_6_12_1_1614 7
  36 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 162 6 1 6 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 162
  (Polychromatic418967fa.accept_11_5_3_8_1_454 5 36 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 36 162 2 2 18 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 36 162 3 1 12 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 36 162 2 1 18 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 36 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 36 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 36 162)))))))))))))))))))))))))))))))))))) (allB_succ 35 162
  (allA_succ_of_accept 34 35 162 (accept_3_4 34 35 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  35 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 35 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 35 162 (Polychromatic418967fa.accept_15_2_5_12_1_369 32 35 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 162 (accept_3_4 31 35 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 35 162 (Polychromatic418967fa.accept_13_4_9_6_1_2376 30 35 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 35 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 35 162 (accept_3_4 28 35 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  35 162 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 35 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 35 162 (Polychromatic418967fa.accept_19_7_16_10_1_2172 26 35 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 162 (accept_3_4 25 35 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 162 (Polychromatic418967fa.accept_15_9_5_12_1_1640 24 35
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 162
  (Polychromatic418967fa.accept_10_3_5_2_1_38 23 35 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 162 (accept_3_4 22 35 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  35 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 35 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 35 162 (Polychromatic418967fa.accept_13_7_9_6_1_148 20 35 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 162 (accept_3_4 19 35 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 162 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 35 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 35 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 162 (accept_3_4 16 35 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  35 162 (Polychromatic418967fa.accept_13_2_9_6_1_501 15 35 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 35 162 (Polychromatic418967fa.accept_13_1_9_6_1_146 14 35 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 162 (accept_3_4 13 35 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 162 (Polychromatic418967fa.accept_21_12_14_15_1_8909 12 35 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 162
  (Polychromatic418967fa.accept_22_11_13_8_1_7242 11 35 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 35 162 (accept_3_4 10 35 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  35 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 35 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 35 162 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 35 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 162 (accept_3_4 7 35 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 35 162 (Polychromatic418967fa.accept_14_6_7_8_1_624 6 35 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 35
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 162 (accept_3_4 4 35 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 162 (Polychromatic418967fa.accept_10_3_5_2_1_38 3
  35 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 162
  (Polychromatic418967fa.accept_13_2_9_6_1_501 2 35 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 162 (accept_3_4 1 35 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  162))))))))))))))))))))))))))))))))))) (allB_succ 34 162 (allA_succ_of_accept 33 34 162
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 34 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 34 162 2 16 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 34 162 (Polychromatic418967fa.accept_15_1_4_12_1_2401 31 34 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 162 2 15 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 162 (accept_3_5 29 34 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34 162 2 14 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 34 162 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 34 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 162 2 13 17 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 162
  (Polychromatic418967fa.accept_19_6_15_10_1_2170 25 34 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 34 162 2 12 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 34 162 (accept_3_5 23 34 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34
  162 2 11 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  34 162 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 34 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 34 162 2 10 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 34 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 34 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 162 2 9 17 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 162 (accept_3_5 17 34 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 34 162 2 8 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 34 162 (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 34 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 162 2 7 17 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 162
  (Polychromatic418967fa.accept_23_13_11_1_1_7158 13 34 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 34 162 2 6 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 34 162 (accept_3_5 11 34 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34
  162 2 5 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  34 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 34 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 34 162 2 4 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 34 162 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 34 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 162 2 3 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 162 (accept_3_5 5 34 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 34 162 2 2 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 34 162 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 34 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 162 2 1 17 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 162
  (Polychromatic418967fa.accept_13_1_8_6_1_1016 1 34 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 162)))))))))))))))))))))))))))))))))) (allB_succ 33 162 (allA_succ_of_accept 32 33 162
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 33 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 33 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 33 162 3 10 11 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 33 162 (Polychromatic418967fa.accept_20_9_13_2_1_8908
  29 33 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 162
  (Polychromatic418967fa.accept_12_4_9_6_1_440 28 33 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 33 162 3 9 11 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 33 162 (Polychromatic418967fa.accept_12_2_9_6_1_439 26 33 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 33 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 162 3 8 11 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 33 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 162 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 33 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 33 162 3 7 11 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 33 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 33 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 33 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 33 162 3 6 11 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 33 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 33 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 162 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 33 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 162 3 5 11 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 162
  (Polychromatic418967fa.accept_12_2_9_6_1_439 14 33 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 33 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 33 162 3 4 11 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 33 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 33 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 162
  (Polychromatic418967fa.accept_7_3_5_1_1_72 10 33 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 33 162 3 3 11 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 33 162 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 33 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 33 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 162 3 2 11 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 162
  (Polychromatic418967fa.accept_10_5_3_2_1_899 5 33 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 33 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 33 162 3 1 11 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 33 162 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 33 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 162
  (Polychromatic418967fa.accept_10_1_3_2_1_220 1 33 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 33 162))))))))))))))))))))))))))))))))) (allB_succ 32 162 (allA_succ_of_accept 31 32 162 (accept_3_4 31 32
  162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32 162 2 15 16 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 32 162
  (Polychromatic418967fa.accept_15_14_2_12_1_2472 29 32 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 32 162 2 14 16 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 32 162 (Polychromatic418967fa.accept_12_3_8_6_1_895 27 32 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 162 2 13 16 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 162 (accept_3_4 25 32 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 162 2 12 16 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 162 (Polychromatic418967fa.accept_17_6_15_9_1_1791 23 32 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 162 2 11 16 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 162
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 32 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 162 2 10 16 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 162 (accept_3_4 19 32 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32
  162 2 9 16 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  32 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 32 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 32 162 2 8 16 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 32 162 (Polychromatic418967fa.accept_12_3_8_6_1_895 15 32 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 162 2 7 16 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 162 (accept_3_4 13 32 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 162 2 6 16 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 32 162 (Polychromatic418967fa.accept_14_11_4_8_1_664 11 32 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 162 2 5 16 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 162
  (Polychromatic418967fa.accept_11_9_10_8_1_444 9 32 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 32 162 2 4 16 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 32 162 (accept_3_4 7 32 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 162
  2 3 16 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32
  162 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 32 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 32 162 2 2 16 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 32 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 32 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 162 2 1 16 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 162 (accept_3_4 1 32 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 162)))))))))))))))))))))))))))))))) (allB_succ 31 162 (allA_succ_of_accept 30 31 162
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 31 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 162 (accept_3_5 29 31 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 162 (Polychromatic418967fa.accept_15_13_1_12_1_1638 28 31 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 162 (Polychromatic418967fa.accept_13_1_5_6_1_1048 27 31 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 162 (accept_3_5 26 31 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 31 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 162
  (Polychromatic418967fa.accept_13_11_5_6_1_519 24 31 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 162 (accept_3_5 23 31 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 162 (Polychromatic418967fa.accept_17_5_14_9_1_5104 22 31 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 31 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 162 (accept_3_5 20 31 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 31 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 162
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 31 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 162 (accept_3_5 17 31 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 31 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 162 (Polychromatic418967fa.accept_24_15_7_18_1_8907 15 31 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 162 (accept_3_5 14 31 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 31 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 162
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 31 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 162 (accept_3_5 11 31 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 162 (Polychromatic418967fa.accept_11_10_9_8_1_1974 10 31 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 31 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 162 (accept_3_5 8 31 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 162 (Polychromatic418967fa.accept_21_7_10_15_1_8906 7 31 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 162
  (Polychromatic418967fa.accept_10_6_1_2_1_874 6 31 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 162 (accept_3_5 5 31 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  162 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 31 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 162 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 31 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 162 (accept_3_5 2 31 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 31 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 162))))))))))))))))))))))))))))))) (allB_succ 30 162
  (allA_succ_of_accept 29 30 162 (Polychromatic418967fa.accept_14_1_2_8_1_655 29 30 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30 162 2 14 15 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 30 162 3 9 10 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 30 162 2 13 15 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 162 (Polychromatic418967fa.accept_20_5_10_2_1_7314
  25 30 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 162 6 4 5 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 162
  (Polychromatic418967fa.accept_13_10_4_6_1_3224 23 30 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 30 162 2 11 15 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 30 162 3 7 10 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 30 162 2 10 15 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 162 (Polychromatic418967fa.accept_21_19_9_15_1_4217 19 30 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 162 6 3 5 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 30 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 162 2 8 15 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 30 162 3 5 10 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 30 162 2 7 15 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 162
  (Polychromatic418967fa.accept_7_6_2_1_1_214 13 30 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 30 162 6 2 5 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 30 162 (Polychromatic418967fa.accept_13_11_4_6_1_1006 11 30 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 162 2 5 15 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 30 162 3 3 10 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 30 162 2 4 15 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 162 (Polychromatic418967fa.accept_13_7_4_6_1_3221 7 30 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 162 6 1 5 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 162
  (Polychromatic418967fa.accept_13_5_4_6_1_2371 5 30 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 30 162 2 2 15 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 30 162 3 1 10 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 30 162 2 1 15 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 30 162 (Polychromatic418967fa.accept_14_1_2_8_1_655 1 30 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 30 162)))))))))))))))))))))))))))))) (allB_succ 29 162 (allA_succ_of_accept
  28 29 162 (accept_3_4 28 29 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 29 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 162 (Polychromatic418967fa.accept_11_4_7_8_1_1926 26 29 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 162 (accept_3_4 25 29 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 162 (Polychromatic418967fa.accept_15_9_14_12_1_913 24 29 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 29 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 162 (accept_3_4 22 29 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 162 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 29 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 162 (Polychromatic418967fa.accept_25_20_4_12_1_8905 20 29 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 162 (accept_3_4 19 29 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 162 (Polychromatic418967fa.accept_13_5_3_6_1_3278 18 29 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 162
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 17 29 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 162 (accept_3_4 16 29 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 29 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 162 (Polychromatic418967fa.accept_13_1_3_6_1_158 14 29 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 162 (accept_3_4 13 29 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 162 (Polychromatic418967fa.accept_20_12_9_2_1_4472 12 29 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 29 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 162 (accept_3_4 10 29 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 162 (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 29 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 162 (Polychromatic418967fa.accept_25_8_4_12_1_8904 8 29 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 162 (accept_3_4 7 29 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 162 (Polychromatic418967fa.accept_21_6_8_15_1_8903 6 29 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 162
  (Polychromatic418967fa.accept_13_5_3_6_1_3278 5 29 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 162 (accept_3_4 4 29 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  162 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 29 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 162 (Polychromatic418967fa.accept_14_2_1_8_1_650 2 29 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 162 (accept_3_4 1 29 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 162))))))))))))))))))))))))))))) (allB_succ 28 162 (allA_succ_of_accept 27 28 162
  (Polychromatic418967fa.accept_12_3_4_6_1_434 27 28 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 28 162 2 13 14 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 28 162 (Polychromatic418967fa.accept_10_5_8_2_1_517 25 28 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 162 2 12 14 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 162 (accept_3_5 23 28 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28 162 2 11 14 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 28 162 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 28 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 28 162 2 10 14 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 28 162
  (Polychromatic418967fa.accept_17_2_11_9_1_1739 19 28 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 28 162 2 9 14 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 28 162 (accept_3_5 17 28 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28
  162 2 8 14 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  28 162 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 28 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 28 162 2 7 14 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 28 162 (Polychromatic418967fa.accept_19_13_9_10_1_2181 13 28 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 162 2 6 14 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 162 (accept_3_5 11 28 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28 162 2 5 14 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 28 162 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 28 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 28 162 2 4 14 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 28 162
  (Polychromatic418967fa.accept_16_7_12_2_1_8902 7 28 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 28 162 2 3 14 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 28 162 (accept_3_5 5 28 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 162
  2 2 14 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 28
  162 (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 28 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 28 162 2 1 14 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 28 162 (Polychromatic418967fa.accept_13_1_2_6_1_515 1 28 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 162)))))))))))))))))))))))))))) (allB_succ 27 162
  (allA_succ_of_accept 26 27 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 27 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 27 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 162 3 8 9 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 162
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 27 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 162 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 27 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 27 162 3 7 9 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 27 162 (Polychromatic418967fa.accept_12_8_3_6_1_909 20 27 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 162
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 27 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 27 162 9 2 3 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 27 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 27 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 27 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 162 3 5 9 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 162
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 27 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 27 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 27 162 3 4 9 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 27 162 (Polychromatic418967fa.accept_19_11_8_10_1_8901 11 27
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 162
  (Polychromatic418967fa.accept_12_10_3_6_1_882 10 27 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 27 162 9 1 3 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 27 162 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 27 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 162 (Polychromatic418967fa.accept_13_7_1_6_1_3287 7 27 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 162 3 2 9 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 27 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 162 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 27 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 27 162 3 1 9 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 27 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 27 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 27 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 27 162))))))))))))))))))))))))))) (allB_succ 26 162 (allA_succ_of_accept 25 26 162 (accept_3_4 25 26 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26 162 2 12 13 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 26 162
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 23 26 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 26 162 2 11 13 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 26 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 26 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 162 2 10 13 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 162 (accept_3_4 19 26 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 162 2 9 13 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 26 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 26 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 162 2 8 13 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 162
  (Polychromatic418967fa.accept_12_3_2_6_1_138 15 26 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 162 2 7 13 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 26 162 (accept_3_4 13 26 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26
  162 2 6 13 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  26 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 26 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 26 162 2 5 13 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 26 162 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 26 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 162 2 4 13 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 162 (accept_3_4 7 26 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 162 2 3 13 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 26 162 (Polychromatic418967fa.accept_19_5_7_10_1_7375 5 26 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 162 2 2 13 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 162
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 26 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 26 162 2 1 13 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 26 162 (accept_3_4 1 26 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  162)))))))))))))))))))))))))) (allB_succ 25 162 (allA_succ_of_accept 24 25 162
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 25 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 162 (accept_3_5 23 25 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 162 (Polychromatic418967fa.accept_15_7_10_12_1_2403 22 25 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 162 (Polychromatic418967fa.accept_15_6_10_12_1_2538 21 25 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 162 (accept_3_5 20 25 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 25 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 162
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 25 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 162 (accept_3_5 17 25 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 162 (Polychromatic418967fa.accept_11_5_3_8_1_454 16 25 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 25 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 162 (accept_3_5 14 25 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 162 (Polychromatic418967fa.accept_10_3_5_2_1_38 13 25 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 162
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 25 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 162 (accept_3_5 11 25 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 25 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 162 (Polychromatic418967fa.accept_15_9_10_12_1_1625 9 25 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 162 (accept_3_5 8 25 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 25 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 162
  (Polychromatic418967fa.accept_11_6_3_8_1_843 6 25 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 162 (accept_3_5 5 25 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  162 (Polychromatic418967fa.accept_14_4_11_8_1_2034 4 25 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 25 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 25 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 162 (accept_3_5 2 25 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 162 (Polychromatic418967fa.accept_16_1_9_2_1_4161 1 25 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 162))))))))))))))))))))))))) (allB_succ 24 162
  (allA_succ_of_accept 23 24 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 24 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 162 2 11 12 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 24 162 3 7 8 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 24 162 2 10 12 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 19
  24 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 162 6 3 4 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 162
  (Polychromatic418967fa.accept_10_7_4_2_1_903 17 24 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 24 162 2 8 12 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 24 162 3 5 8 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 24 162 2 7 12 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 24 162 (Polychromatic418967fa.accept_19_13_5_10_1_4609 13 24 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 162 6 2 4 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 24 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 162 2 5 12 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 24 162 3 3 8 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 24 162 2 4 12 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 162
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 24 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 162 6 1 4 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 24 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 162 2 2 12 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 24 162 3 1 8 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 24 162 2 1 12 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 162 (Polychromatic418967fa.accept_21_1_3_15_1_5797 1 24 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 162)))))))))))))))))))))))) (allB_succ 23
  162 (allA_succ_of_accept 22 23 162 (accept_3_4 22 23 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 23 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 23 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 23 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 23 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 162 (accept_3_4 19 23 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 23 162 (Polychromatic418967fa.accept_13_5_10_6_1_2361 18 23 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 23 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 23 162 (accept_3_4 16 23 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  23 162 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 23 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 23 162 (Polychromatic418967fa.accept_19_14_4_10_1_3344 14 23 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 162 (accept_3_4 13 23 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 162 (Polychromatic418967fa.accept_13_12_10_6_1_3212 12 23
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 162
  (Polychromatic418967fa.accept_10_1_3_2_1_220 11 23 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 162 (accept_3_4 10 23 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 23 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 23 162 (Polychromatic418967fa.accept_17_8_6_9_1_7768 8 23 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 162 (accept_3_4 7 23 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 23 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 23 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 23
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 162 (accept_3_4 4 23 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 3
  23 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 162
  (Polychromatic418967fa.accept_13_2_10_6_1_1676 2 23 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 23 162 (accept_3_4 1 23 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23
  162))))))))))))))))))))))) (allB_succ 22 162 (allA_succ_of_accept 21 22 162
  (Polychromatic418967fa.accept_12_9_10_6_1_872 21 22 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 22 162 2 10 11 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 22 162 (Polychromatic418967fa.accept_15_4_7_12_1_5538 19 22 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 162 2 9 11 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 162 (accept_3_5 17 22 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 22 162 2 8 11 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 22 162 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 22 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 162 2 7 11 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 162 (Polychromatic418967fa.accept_17_13_5_9_1_1762
  13 22 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 162 2 6 11 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 162 (accept_3_5 11
  22 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22 162 2 5 11 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 22 162
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 22 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 22 162 2 4 11 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 22 162 (Polychromatic418967fa.accept_13_7_9_6_1_148 7 22 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 162 2 3 11 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 162 (accept_3_5 5 22 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 22 162 2 2 11 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 22 162 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 22 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 162 2 1 11 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 162 (Polychromatic418967fa.accept_13_1_9_6_1_146 1
  22 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 162)))))))))))))))))))))) (allB_succ
  21 162 (allA_succ_of_accept 20 21 162 (Polychromatic418967fa.accept_11_9_10_8_1_444 20 21 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 19
  21 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 162 3 6 7 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 162
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 17 21 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 162 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 21 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 162 3 5 7 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 21 162 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 21 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 162
  (Polychromatic418967fa.accept_10_3_1_2_1_521 13 21 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 21 162 3 4 7 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 21 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 21 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 162 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 21
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 162 3 3 7 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 162
  (Polychromatic418967fa.accept_12_8_9_6_1_127 8 21 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 21 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 21 162 3 2 7 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 162 (Polychromatic418967fa.accept_15_5_6_12_1_916 5 21 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 162
  (Polychromatic418967fa.accept_12_4_9_6_1_440 4 21 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 21 162 3 1 7 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 21 162 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 21 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 162 (Polychromatic418967fa.accept_13_1_8_6_1_1016 1 21 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 162))))))))))))))))))))) (allB_succ 20 162
  (allA_succ_of_accept 19 20 162 (accept_3_4 19 20 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20
  162 2 9 10 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  20 162 (Polychromatic418967fa.accept_13_4_7_6_1_2359 17 20 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 20 162 2 8 10 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 20 162 (Polychromatic418967fa.accept_12_3_8_6_1_895 15 20 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 162 2 7 10 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 162 (accept_3_4 13 20 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 20 162 2 6 10 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 20 162 (Polychromatic418967fa.accept_17_11_3_9_1_6387 11 20 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 162 2 5 10 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 162
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 20 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 20 162 2 4 10 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 20 162 (accept_3_4 7 20 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 162
  2 3 10 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20
  162 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 20 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 20 162 2 2 10 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 20 162 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 20 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 162 2 1 10 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 162 (accept_3_4 1 20 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 162)))))))))))))))))))) (allB_succ 19 162 (allA_succ_of_accept 18 19 162
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 19 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 162 (accept_3_5 17 19 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 162 (Polychromatic418967fa.accept_15_1_4_12_1_2401 16 19 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 162 (Polychromatic418967fa.accept_16_15_3_2_1_4170 15 19 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 162 (accept_3_5 14 19 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 19 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 162
  (Polychromatic418967fa.accept_20_12_19_2_1_4421 12 19 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 162 (accept_3_5 11 19 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 19 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 19 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 162 (accept_3_5 8 19 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 162 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 19 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 162
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 19 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 162 (accept_3_5 5 19 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  162 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 19 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 19 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 162 (accept_3_5 2 19 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 19 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 162))))))))))))))))))) (allB_succ 18 162 (allA_succ_of_accept 17
  18 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 18 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 18 162 2 8 9 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 18 162 3 5 6 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 18 162 2 7 9 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 18 162 (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 18 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 162 6 2 3 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 162
  (Polychromatic418967fa.accept_13_11_5_6_1_519 11 18 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 18 162 2 5 9 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 18 162 9 1 2 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 18 162 2 4 9 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 18 162 (Polychromatic418967fa.accept_15_7_3_12_1_365 7 18 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 162 6 1 3 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 18 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 162 2 2 9 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 18 162 3 1 6 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 18 162 2 1 9 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 162
  (Polychromatic418967fa.accept_13_1_5_6_1_1048 1 18 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 162)))))))))))))))))) (allB_succ 17 162 (allA_succ_of_accept 16 17 162 (accept_3_4 16 17 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 17 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 162
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 17 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 162 (accept_3_4 13 17 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 17 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 17 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 162 (accept_3_4 10 17 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 17 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 162
  (Polychromatic418967fa.accept_19_8_17_10_1_8900 8 17 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 162 (accept_3_4 7 17 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  162 (Polychromatic418967fa.accept_15_6_2_12_1_885 6 17 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 17 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 17 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 162 (accept_3_4 4 17 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 17 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 162
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 17 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 162 (accept_3_4 1 17 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  162))))))))))))))))) (allB_succ 16 162 (allA_succ_of_accept 15 16 162 (Polychromatic418967fa.accept_12_3_4_6_1_434 15
  16 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 16 162 2 7 8 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 16 162
  (Polychromatic418967fa.accept_7_6_2_1_1_214 13 16 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 16 162 2 6 8 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 16 162 (accept_3_5 11 16 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 16
  162 2 5 8 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 16
  162 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 16 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 16 162 2 4 8 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 16 162 (Polychromatic418967fa.accept_19_7_16_10_1_2172 7 16 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 162 2 3 8 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 162 (accept_3_5 5 16 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 16 162 2 2 8 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 16 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 16 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 16 162 2 1 8 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 16 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 1
  16 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 162)))))))))))))))) (allB_succ 15 162
  (allA_succ_of_accept 14 15 162 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 15 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 15 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 162 3 4 5 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 162
  (Polychromatic418967fa.accept_19_11_15_10_1_7406 11 15 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 15 162 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 15 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 15 162 3 3 5 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 15 162 (Polychromatic418967fa.accept_10_8_5_2_1_881 8
  15 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 162
  (Polychromatic418967fa.accept_10_7_5_2_1_880 7 15 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 15 162 3 2 5 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 15 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 15 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 162 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 15 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 162 3 1 5 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 162
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 15 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 15 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 15 162))))))))))))))) (allB_succ 14 162 (allA_succ_of_accept 13 14 162
  (accept_3_4 13 14 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 162 2 6 7 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 162
  (Polychromatic418967fa.accept_15_11_14_12_1_2458 11 14 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 14 162 2 5 7 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 14 162 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 14 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 162 2 4 7 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 14 162 (accept_3_4 7 14 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 14 162 2 3 7 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 14 162 (Polychromatic418967fa.accept_11_5_3_8_1_454 5 14 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 162 2 2 7 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 162
  (Polychromatic418967fa.accept_12_3_2_6_1_138 3 14 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 14 162 2 1 7 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 14 162 (accept_3_4 1 14 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14
  162)))))))))))))) (allB_succ 13 162 (allA_succ_of_accept 12 13 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 13
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 13 162 (accept_3_5 11 13 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 13 162
  (Polychromatic418967fa.accept_15_10_13_12_1_3384 10 13 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 13 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 162 (accept_3_5 8 13 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 13 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 162
  (Polychromatic418967fa.accept_19_6_13_10_1_8899 6 13 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 162 (accept_3_5 5 13 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  162 (Polychromatic418967fa.accept_17_4_13_9_1_921 4 13 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 13 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 13 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 162 (accept_3_5 2 13 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 162 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 13 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 162))))))))))))) (allB_succ 12 162
  (allA_succ_of_accept 11 12 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 12 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 162 2 5 6 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 12 162 3 3 4 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 12 162 2 4 6 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 162 (Polychromatic418967fa.accept_13_7_12_6_1_1039 7 12 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 162 6 1 2 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 162
  (Polychromatic418967fa.accept_13_5_12_6_1_508 5 12 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 12 162 2 2 6 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 12 162 3 1 4 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 12 162 2 1 6 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 12 162 (Polychromatic418967fa.accept_16_1_12_2_1_2136 1 12 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 162)))))))))))) (allB_succ 11 162 (allA_succ_of_accept 10 11 162
  (accept_3_4 10 11 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 11 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 162 (Polychromatic418967fa.accept_13_8_11_6_1_1035 8 11 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 162 (accept_3_4 7 11 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 162 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 11 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 11
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 162 (accept_3_4 4 11 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 11
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 162
  (Polychromatic418967fa.accept_17_2_11_9_1_1739 2 11 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 162 (accept_3_4 1 11 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  162))))))))))) (allB_succ 10 162 (allA_succ_of_accept 9 10 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 10 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 10 162 2 4 5 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 10 162
  (Polychromatic418967fa.accept_15_7_10_12_1_2403 7 10 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 10 162 2 3 5 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 10 162 (accept_3_5 5 10 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 10 162
  2 2 5 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 10 162
  (Polychromatic418967fa.accept_12_3_10_6_1_442 3 10 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 10 162 2 1 5 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 10 162 (Polychromatic418967fa.accept_17_1_10_9_1_3884 1 10 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 10 162)))))))))) (allB_succ 9 162 (allA_succ_of_accept 8 9 162
  (Polychromatic418967fa.accept_12_8_9_6_1_127 8 9 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 9 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 162 3 2 3 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 162 (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 9 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 162
  (Polychromatic418967fa.accept_12_4_9_6_1_440 4 9 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 9 162 3 1 3 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 9 162 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 9 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 162 (Polychromatic418967fa.accept_10_1_9_2_1_45 1 9 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 162))))))))) (allB_succ 8 162
  (allA_succ_of_accept 7 8 162 (accept_3_4 7 8 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 8 162 2
  3 4 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 8 162
  (Polychromatic418967fa.accept_10_5_8_2_1_517 5 8 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 8 162 2 2 4 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 8 162 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 8 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 162 2 1 4 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 162 (accept_3_4 1 8 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 162)))))))) (allB_succ 7 162 (allA_succ_of_accept 6 7 162
  (Polychromatic418967fa.accept_14_6_7_8_1_624 6 7 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 162 (accept_3_5 5 7 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 162
  (Polychromatic418967fa.accept_10_4_7_2_1_211 4 7 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 162 (Polychromatic418967fa.accept_15_3_7_12_1_372 3 7 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 162 (accept_3_5 2 7 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 7 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 162))))))) (allB_succ 6 162 (allA_succ_of_accept 5 6 162
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 6 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 6 162 2 2 3 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 6 162 3 1 2 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 6 162 2 1 3 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 6 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 162)))))) (allB_succ 5 162 (allA_succ_of_accept 4 5 162 (accept_3_4 4 5
  162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 3
  5 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 162
  (Polychromatic418967fa.accept_11_2_5_8_1_470 2 5 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 162 (accept_3_4 1 5 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 162)))))
  (allB_succ 4 162 (allA_succ_of_accept 3 4 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 4 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 162 2 1 2 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 162 (Polychromatic418967fa.accept_11_1_4_8_1_1918 1 4
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 4 162)))) (allB_succ 3 162
  (allA_succ_of_accept 2 3 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 3 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 3 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 162))) (allB_succ 2 162 (allA_succ_of_accept
  1 2 162 (accept_3_4 1 2 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 162)) (allB_two
  162)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


