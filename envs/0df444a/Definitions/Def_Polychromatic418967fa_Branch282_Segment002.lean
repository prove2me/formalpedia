-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch282_Segment002
-- name    : Polychromatic418967fa_Branch282_Segment002
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:58:42.235559+00:00
-- url     : https://prove2.me/theorems/92a76f22-79f4-4fbf-96d1-c71fb641dd17
-- title:
--   Polychromatic branch proof segment
-- statement:
--   Checked segment of the pinned Polychromatic branch proof. Kernel types, definition values and allowed axioms match the original proof.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch282_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_282_segment_002 : allB 183 282 :=
  allB_succ' 101 182 282 (Eq.refl Bool.true) (allA_succ_of_gcd 100 182 282 2 50 91 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 182 282
  (Polychromatic418967fa.accept_12_3_2_6_1_138 99 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 182 282 2 49 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 182 282 (accept_3_4 97 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 182 282 2 48 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 182 282 (Polychromatic418967fa.accept_9_5_2_3_1_194 95 182 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 182 282 2 47 91 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 182 282
  (Polychromatic418967fa.accept_12_9_2_6_1_455 93 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 182 282 2 46 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 182 282 (accept_3_4 91 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 182 282 2 45 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 182 282 (Polychromatic418967fa.accept_9_8_2_3_1_447 89 182 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 182 282 2 44 91 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 182 282
  (Polychromatic418967fa.accept_9_6_2_3_1_771 87 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 182 282 2 43 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 182 282 (accept_3_4 85 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 182 282 2 42 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 182 282 (Polychromatic418967fa.accept_21_20_14_9_1_11573 83 182 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 182 282 2 41 91 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 182 282
  (Polychromatic418967fa.accept_12_9_2_6_1_455 81 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 182 282 2 40 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 182 282 (accept_3_4 79 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 182 282 2 39 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 182 282 (Polychromatic418967fa.accept_9_5_2_3_1_194 77 182 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 182 282 2 38 91 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 182 282
  (Polychromatic418967fa.accept_12_3_2_6_1_138 75 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 182 282 2 37 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 182 282 (accept_3_4 73 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 182 282 2 36 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 182 282 (Polychromatic418967fa.accept_9_8_2_3_1_447 71 182 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 182 282 2 35 91 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 182 282
  (Polychromatic418967fa.accept_9_6_2_3_1_771 69 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 182 282 2 34 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 182 282 (accept_3_4 67 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 182 282 2 33 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 182 282 (Polychromatic418967fa.accept_15_5_2_12_1_2543 65 182 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 182 282 2 32 91 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 182 282
  (Polychromatic418967fa.accept_12_3_2_6_1_138 63 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 182 282 2 31 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 182 282 (accept_3_4 61 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 182 282 2 30 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 182 282 (Polychromatic418967fa.accept_9_5_2_3_1_194 59 182 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 182 282 2 29 91 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 182 282
  (Polychromatic418967fa.accept_12_9_2_6_1_455 57 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 182 282 2 28 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 182 282 (accept_3_4 55 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 182 282 2 27 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 182 282 (Polychromatic418967fa.accept_9_8_2_3_1_447 53 182 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 182 282 2 26 91 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 182 282
  (Polychromatic418967fa.accept_9_6_2_3_1_771 51 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 182 282 2 25 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 182 282 (accept_3_4 49 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 182 282 2 24 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 182 282 (Polychromatic418967fa.accept_21_5_14_9_1_2410 47 182 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 182 282 2 23 91 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 182 282
  (Polychromatic418967fa.accept_11_1_6_7_1_116 45 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 182 282 2 22 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 182 282 (accept_3_4 43 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 182 282 2 21 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 182 282 (Polychromatic418967fa.accept_9_5_2_3_1_194 41 182 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 182 282 2 20 91 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 182 282
  (Polychromatic418967fa.accept_12_3_2_6_1_138 39 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 182 282 2 19 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 182 282 (accept_3_4 37 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 182 282 2 18 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 182 282 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 182 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 182 282 2 17 91 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 182 282
  (Polychromatic418967fa.accept_9_6_2_3_1_771 33 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 182 282 2 16 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 182 282 (accept_3_4 31 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 182 282 2 15 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 182 282 (Polychromatic418967fa.accept_15_14_2_12_1_2472 29 182 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 182 282 2 14 91 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 182 282
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 182 282 2 13 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 182 282 (accept_3_4 25 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 182 282 2 12 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 182 282 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 182 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 182 282 2 11 91 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 182 282
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 182 282 2 10 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 182 282 (accept_3_4 19 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 182 282 2 9 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 182 282 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 182 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 182 282 2 8 91 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 182 282
  (Polychromatic418967fa.accept_9_6_2_3_1_771 15 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 182 282 2 7 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 182 282 (accept_3_4 13 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 182 282 2 6 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 182 282 (Polychromatic418967fa.accept_22_11_6_18_1_6402 11 182 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 182 282 2 5 91 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 182 282
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 182 282 2 4 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 182 282 (accept_3_4 7 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 182
  282 2 3 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  182 282 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 182 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 182 282 2 2 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 182 282 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 182 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 182 282 2 1 91 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 182 282 (accept_3_4 1 182 282
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182
  282))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  102 181 282 (Eq.refl Bool.true) (allA_succ_of_accept 101 181 282 (accept_3_5 101 181 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 181 282 (Polychromatic418967fa.accept_19_5_10_16_1_6507 100 181 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 181 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 99 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 181 282 (accept_3_5 98 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 181 282 (Polychromatic418967fa.accept_9_7_1_3_1_443 97 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 181 282 (Polychromatic418967fa.accept_9_6_1_3_1_191 96 181 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 181 282 (accept_3_5 95 181 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 181 282 (Polychromatic418967fa.accept_7_3_6_2_1_90 94 181 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 181 282
  (Polychromatic418967fa.accept_10_3_1_2_1_521 93 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 181 282 (accept_3_5 92 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 181 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 181 282 (Polychromatic418967fa.accept_21_6_13_9_1_12985 90 181 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 181 282 (accept_3_5 89 181 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 181 282 (Polychromatic418967fa.accept_7_4_6_2_1_451 88 181 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 181 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 87 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 181 282 (accept_3_5 86 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 181 282 (Polychromatic418967fa.accept_7_1_6_2_1_18 85 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 181 282 (Polychromatic418967fa.accept_19_8_10_16_1_9418 84 181 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 181 282 (accept_3_5 83 181 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 181 282 (Polychromatic418967fa.accept_19_6_10_16_1_7989 82 181
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 181 282
  (Polychromatic418967fa.accept_7_4_6_2_1_451 81 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 181 282 (accept_3_5 80 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 181 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 181 282 (Polychromatic418967fa.accept_7_1_6_2_1_18 78 181 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 181 282 (accept_3_5 77 181 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 181 282 (Polychromatic418967fa.accept_9_4_1_3_1_190 76 181 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 181 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 181 282 (accept_3_5 74 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 181 282 (Polychromatic418967fa.accept_7_3_6_2_1_90 73 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 181 282 (Polychromatic418967fa.accept_17_4_11_10_1_5167 72 181 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 181 282 (accept_3_5 71 181 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 181 282 (Polychromatic418967fa.accept_9_7_1_3_1_443 70 181 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 181 282
  (Polychromatic418967fa.accept_9_6_1_3_1_191 69 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 181 282 (accept_3_5 68 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 181 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 181 282 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 181 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 181 282 (accept_3_5 65 181 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 181 282 (Polychromatic418967fa.accept_7_1_6_2_1_18 64 181 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 181 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 181 282 (accept_3_5 62 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 181 282 (Polychromatic418967fa.accept_9_7_1_3_1_443 61 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 181 282 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 181 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 181 282 (accept_3_5 59 181 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 181 282 (Polychromatic418967fa.accept_9_4_1_3_1_190 58 181 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 181 282
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 181 282 (accept_3_5 56 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 181 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 181 282 (Polychromatic418967fa.accept_17_3_11_10_1_7787 54 181 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 181 282 (accept_3_5 53 181 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 181 282 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 181 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 181 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 181 282 (accept_3_5 50 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 181 282 (Polychromatic418967fa.accept_9_4_1_3_1_190 49 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 181 282 (Polychromatic418967fa.accept_21_6_13_9_1_12985 48 181 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 181 282 (accept_3_5 47 181 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 181 282 (Polychromatic418967fa.accept_7_4_6_2_1_451 46 181 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 181 282
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 181 282 (accept_3_5 44 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 181 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 181 282 (Polychromatic418967fa.accept_9_6_1_3_1_191 42 181 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 181 282 (accept_3_5 41 181 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 181 282 (Polychromatic418967fa.accept_9_4_1_3_1_190 40 181 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 181 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 181 282 (accept_3_5 38 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 181 282 (Polychromatic418967fa.accept_17_3_11_10_1_7787 37 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 181 282 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 181 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 181 282 (accept_3_5 35 181 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 181 282 (Polychromatic418967fa.accept_9_7_1_3_1_443 34 181 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 181 282
  (Polychromatic418967fa.accept_9_6_1_3_1_191 33 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 181 282 (accept_3_5 32 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 181 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 181 282 (Polychromatic418967fa.accept_16_14_5_10_1_3622 30 181 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 181 282 (accept_3_5 29 181 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 181 282 (Polychromatic418967fa.accept_15_13_1_12_1_1638 28 181
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 181 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 181 282 (accept_3_5 26 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 181 282 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 181 282 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 181 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 181 282 (accept_3_5 23 181 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 181 282 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 181 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 181 282
  (Polychromatic418967fa.accept_13_8_12_9_1_1168 21 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 181 282 (accept_3_5 20 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 181 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 181 282 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 181 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 181 282 (accept_3_5 17 181 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 181 282 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 181 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 181 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 181 282 (accept_3_5 14 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 181 282 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 181 282 (Polychromatic418967fa.accept_16_12_5_10_1_3561 12 181 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 282 (accept_3_5 11 181 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 282 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 181 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 282
  (Polychromatic418967fa.accept_10_9_1_2_1_522 9 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 181 282 (accept_3_5 8 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  181 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 181 282 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 181 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 282 (accept_3_5 5 181 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 282 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 181 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 282 (accept_3_5 2 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 282 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 181 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181
  282)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  103 180 282 (Eq.refl Bool.true) (allA_succ_of_gcd 102 180 282 6 17 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 180 282 (Polychromatic418967fa.accept_7_3_5_2_1_17
  101 180 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 180 282 2 50 90 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 180 282 3 33 60
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 180 282 2 49
  90 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 180 282
  (Polychromatic418967fa.accept_21_13_12_9_1_5323 97 180 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 96 180 282 6 16 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 95 180 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 95 180 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 180 282 2 47 90 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 180 282 3 31 60 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 180 282 2 46 90 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 180 282
  (Polychromatic418967fa.accept_11_3_4_7_1_114 91 180 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 180 282 6 15 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 180 282 (Polychromatic418967fa.accept_21_5_12_9_1_11589 89 180 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 180 282 2 44 90 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 180 282 3 29 60 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 180 282 2 43 90 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 180 282
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 85 180 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 180 282 6 14 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 180 282 (Polychromatic418967fa.accept_19_7_9_16_1_10774 83 180 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 180 282 2 41 90 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 180 282 3 27 60 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 180 282 2 40 90 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 180 282
  (Polychromatic418967fa.accept_13_1_11_9_1_1857 79 180 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 180 282 6 13 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 180 282 (Polychromatic418967fa.accept_14_7_12_2_1_2502 77 180 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 180 282 2 38 90 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 180 282 3 25 60 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 180 282 2 37 90 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 180 282
  (Polychromatic418967fa.accept_7_3_5_2_1_17 73 180 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 180 282 6 12 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 180 282 (Polychromatic418967fa.accept_19_14_9_16_1_7969 71 180 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 180 282 2 35 90 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 180 282 3 23 60 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 180 282 2 34 90 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 180 282
  (Polychromatic418967fa.accept_7_4_5_2_1_243 67 180 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 180 282 6 11 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 180 282 (Polychromatic418967fa.accept_19_8_9_16_1_9406 65 180 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 180 282 2 32 90 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 180 282 3 21 60 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 180 282 2 31 90 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 180 282
  (Polychromatic418967fa.accept_19_4_9_16_1_3811 61 180 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 180 282 6 10 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 180 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 180 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 180 282 2 29 90 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 180 282 3 19 60 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 180 282 2 28 90 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 180 282
  (Polychromatic418967fa.accept_21_13_12_9_1_5323 55 180 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 180 282 6 9 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 180 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 180 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 180 282 2 26 90 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 180 282 3 17 60 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 180 282 2 25 90 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 180 282
  (Polychromatic418967fa.accept_14_7_12_2_1_2502 49 180 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 180 282 6 8 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 180 282 (Polychromatic418967fa.accept_11_3_4_7_1_114 47 180 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 180 282 2 23 90 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 180 282 3 15 60 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 180 282 2 22 90 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 180 282
  (Polychromatic418967fa.accept_21_1_12_9_1_8469 43 180 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 180 282 6 7 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 180 282 (Polychromatic418967fa.accept_11_8_4_7_1_1303 41 180 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 180 282 2 20 90 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 180 282 3 13 60 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 180 282 2 19 90 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 180 282
  (Polychromatic418967fa.accept_19_18_9_16_1_6524 37 180 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 180 282 6 6 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 180 282 (Polychromatic418967fa.accept_14_7_12_2_1_2502 35 180 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 180 282 2 17 90 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 180 282 3 11 60 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 180 282 2 16 90 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 180 282
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 180 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 180 282 6 5 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 180 282 (Polychromatic418967fa.accept_19_10_9_16_1_5085 29 180 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 180 282 2 14 90 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 180 282 3 9 60 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 180 282 2 13 90 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 180 282
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 180 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 180 282 6 4 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 180 282 (Polychromatic418967fa.accept_19_4_9_16_1_3811 23 180 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 180 282 2 11 90 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 180 282 3 7 60 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 180 282 2 10 90 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 180 282
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 19 180 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 180 282 6 3 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 180 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 180 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 180 282 2 8 90 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 180 282 3 5 60 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 180 282 2 7 90 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 180 282
  (Polychromatic418967fa.accept_21_13_12_9_1_5323 13 180 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 180 282 6 2 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 180 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 180 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 180 282 2 5 90 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 180 282 3 3 60 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 180 282 2 4 90 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 180 282
  (Polychromatic418967fa.accept_13_7_11_9_1_1858 7 180 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 180 282 6 1 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 180 282 (Polychromatic418967fa.accept_21_5_12_9_1_11589 5 180 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 180 282 2 2 90 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 180 282 3 1 60 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 180 282 2 1 90 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 180 282 (Polychromatic418967fa.accept_13_1_11_9_1_1857
  1 180 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180
  282))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 179 282 (Eq.refl Bool.true) (allA_succ_of_accept 103 179 282 (accept_3_4 103 179 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 179 282 (Polychromatic418967fa.accept_19_7_8_16_1_6490 102 179 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 179 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 101 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 179 282 (accept_3_4 100 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 179 282 (Polychromatic418967fa.accept_15_9_14_12_1_913 99 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 179 282 (Polychromatic418967fa.accept_11_10_3_7_1_2564 98 179 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 179 282 (accept_3_4 97 179 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 179 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 96 179 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 179 282
  (Polychromatic418967fa.accept_9_5_8_3_1_437 95 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 179 282 (accept_3_4 94 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 179 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 179 282 (Polychromatic418967fa.accept_9_2_8_3_1_181 92 179 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 179 282 (accept_3_4 91 179 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 179 282 (Polychromatic418967fa.accept_7_6_4_2_1_236 90 179 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 179 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 179 282 (accept_3_4 88 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 179 282 (Polychromatic418967fa.accept_9_6_8_3_1_183 87 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 179 282 (Polychromatic418967fa.accept_9_5_8_3_1_437 86 179 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 179 282 (accept_3_4 85 179 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 179 282 (Polychromatic418967fa.accept_13_6_10_9_1_4329 84 179 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 179 282
  (Polychromatic418967fa.accept_7_6_4_2_1_236 83 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 179 282 (accept_3_4 82 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 179 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 179 282 (Polychromatic418967fa.accept_23_11_18_6_1_15805 80 179 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 179 282 (accept_3_4 79 179 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 179 282 (Polychromatic418967fa.accept_9_6_8_3_1_183 78 179 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 179 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 179 282 (accept_3_4 76 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 179 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 75 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 179 282 (Polychromatic418967fa.accept_9_2_8_3_1_181 74 179 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 179 282 (accept_3_4 73 179 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 179 282 (Polychromatic418967fa.accept_19_15_8_16_1_10745 72 179 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 179 282
  (Polychromatic418967fa.accept_10_1_9_2_1_45 71 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 179 282 (accept_3_4 70 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 179 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 179 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 68 179 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 179 282 (accept_3_4 67 179 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 179 282 (Polychromatic418967fa.accept_13_1_10_9_1_215 66 179 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 179 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 179 282 (accept_3_4 64 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 179 282 (Polychromatic418967fa.accept_18_9_17_12_1_462 63 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 179 282 (Polychromatic418967fa.accept_7_6_4_2_1_236 62 179 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 179 282 (accept_3_4 61 179 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 179 282 (Polychromatic418967fa.accept_9_6_8_3_1_183 60 179 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 179 282
  (Polychromatic418967fa.accept_9_5_8_3_1_437 59 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 179 282 (accept_3_4 58 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 179 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 179 282 (Polychromatic418967fa.accept_9_2_8_3_1_181 56 179 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 179 282 (accept_3_4 55 179 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 179 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 179 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 179 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 179 282 (accept_3_4 52 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 179 282 (Polychromatic418967fa.accept_9_6_8_3_1_183 51 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 179 282 (Polychromatic418967fa.accept_9_5_8_3_1_437 50 179 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 179 282 (accept_3_4 49 179 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 179 282 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 179 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 179 282
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 179 282 (accept_3_4 46 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 179 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 179 282 (Polychromatic418967fa.accept_16_12_3_10_1_3524 44 179 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 179 282 (accept_3_4 43 179 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 179 282 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 179 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 179 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 179 282 (accept_3_4 40 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 179 282 (Polychromatic418967fa.accept_15_9_14_12_1_913 39 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 179 282 (Polychromatic418967fa.accept_9_2_8_3_1_181 38 179 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 179 282 (accept_3_4 37 179 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 179 282 (Polychromatic418967fa.accept_19_17_8_16_1_12029 36 179 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 179 282
  (Polychromatic418967fa.accept_17_1_9_10_1_1864 35 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 179 282 (accept_3_4 34 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 179 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 179 282 (Polychromatic418967fa.accept_9_5_8_3_1_437 32 179 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 179 282 (accept_3_4 31 179 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 179 282 (Polychromatic418967fa.accept_17_13_9_10_1_2888 30 179 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 179 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 179 282 (accept_3_4 28 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 179 282 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 179 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 179 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 179 282 (accept_3_4 25 179 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 179 282 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 179 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 179 282
  (Polychromatic418967fa.accept_9_5_8_3_1_437 23 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 179 282 (accept_3_4 22 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 179 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 179 282 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 179 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 179 282 (accept_3_4 19 179 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 179 282 (Polychromatic418967fa.accept_17_1_9_10_1_1864 18 179 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 179 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 179 282 (accept_3_4 16 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 179 282 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 179 282 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 179 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 179 282 (accept_3_4 13 179 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 179 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 179 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 179 282
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 179 282 (accept_3_4 10 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  179 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 179 282 (Polychromatic418967fa.accept_24_8_11_18_1_8976 8 179 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 179 282 (accept_3_4 7 179 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 179 282 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 179 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 179 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 179 282 (accept_3_4 4 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  179 282 (Polychromatic418967fa.accept_17_3_9_10_1_9045 3 179 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 179 282 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 179 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 179 282 (accept_3_4 1 179 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 179
  282))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 105 178 282 (Eq.refl Bool.true) (allA_succ_of_gcd 104 178 282 2 52 89 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 178 282
  (Polychromatic418967fa.accept_7_5_3_2_1_249 103 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 178 282 2 51 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 178 282 (accept_3_5 101 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 178 282 2 50 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 178 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 99 178 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 178 282 2 49 89 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 178 282
  (Polychromatic418967fa.accept_7_6_3_2_1_461 97 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 178 282 2 48 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 178 282 (accept_3_5 95 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 178 282 2 47 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 178 282 (Polychromatic418967fa.accept_12_9_10_6_1_872 93 178 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 178 282 2 46 89 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 178 282
  (Polychromatic418967fa.accept_9_1_7_3_1_41 91 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 178 282 2 45 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 178 282 (accept_3_5 89 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 178 282 2 44 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 178 282 (Polychromatic418967fa.accept_9_6_7_3_1_436 87 178 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 178 282 2 43 89 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 178 282
  (Polychromatic418967fa.accept_7_1_3_2_1_13 85 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 178 282 2 42 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 178 282 (accept_3_5 83 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 178 282 2 41 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 178 282 (Polychromatic418967fa.accept_12_9_10_6_1_872 81 178 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 178 282 2 40 89 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 178 282
  (Polychromatic418967fa.accept_21_16_10_9_1_9965 79 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 178 282 2 39 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 178 282 (accept_3_5 77 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 178 282 2 38 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 178 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 178 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 178 282 2 37 89 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 178 282
  (Polychromatic418967fa.accept_9_1_7_3_1_41 73 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 178 282 2 36 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 178 282 (accept_3_5 71 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 178 282 2 35 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 178 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 178 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 178 282 2 34 89 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 178 282
  (Polychromatic418967fa.accept_9_4_7_3_1_43 67 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 178 282 2 33 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 178 282 (accept_3_5 65 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 178 282 2 32 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 178 282 (Polychromatic418967fa.accept_12_3_10_6_1_442 63 178 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 178 282 2 31 89 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 178 282
  (Polychromatic418967fa.accept_7_5_3_2_1_249 61 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 178 282 2 30 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 178 282 (accept_3_5 59 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 178 282 2 29 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 178 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 178 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 178 282 2 28 89 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 178 282
  (Polychromatic418967fa.accept_7_6_3_2_1_461 55 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 178 282 2 27 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 178 282 (accept_3_5 53 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 178 282 2 26 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 178 282 (Polychromatic418967fa.accept_9_6_7_3_1_436 51 178 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 178 282 2 25 89 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 178 282
  (Polychromatic418967fa.accept_9_4_7_3_1_43 49 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 178 282 2 24 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 178 282 (accept_3_5 47 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 178 282 2 23 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 178 282 (Polychromatic418967fa.accept_10_5_8_2_1_517 45 178 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 178 282 2 22 89 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 178 282
  (Polychromatic418967fa.accept_7_1_3_2_1_13 43 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 178 282 2 21 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 178 282 (accept_3_5 41 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 178 282 2 20 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 178 282 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 178 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 178 282 2 19 89 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 178 282
  (Polychromatic418967fa.accept_9_1_7_3_1_41 37 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 178 282 2 18 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 178 282 (accept_3_5 35 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 178 282 2 17 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 178 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 178 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 178 282 2 16 89 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 178 282
  (Polychromatic418967fa.accept_9_4_7_3_1_43 31 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 178 282 2 15 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 178 282 (accept_3_5 29 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 178 282 2 14 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 178 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 178 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 178 282 2 13 89 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 178 282
  (Polychromatic418967fa.accept_10_5_8_2_1_517 25 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 178 282 2 12 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 178 282 (accept_3_5 23 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 178 282 2 11 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 178 282 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 178 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 178 282 2 10 89 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 178 282
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 178 282 2 9 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 178 282 (accept_3_5 17 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 178 282 2 8 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 178 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 178 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 178 282 2 7 89 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 178 282
  (Polychromatic418967fa.accept_7_6_3_2_1_461 13 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 178 282 2 6 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 178 282 (accept_3_5 11 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 178 282 2 5 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 178 282 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 178 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 178 282 2 4 89 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 178 282
  (Polychromatic418967fa.accept_20_7_18_2_1_10451 7 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 178 282 2 3 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 178 282 (accept_3_5 5 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 178
  282 2 2 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  178 282 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 178 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 178 282 2 1 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 178 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 178 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178
  282)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 106 177 282 (Eq.refl Bool.true) (allA_succ_of_gcd 105 177 282 3 35 59 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 177 282
  (Polychromatic418967fa.accept_9_5_6_3_1_40 104 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 177 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 103 177 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 177 282 3 34 59 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 177 282 (Polychromatic418967fa.accept_9_2_6_3_1_178
  101 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 177 282
  (Polychromatic418967fa.accept_9_1_6_3_1_177 100 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 177 282 3 33 59 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 177 282 (Polychromatic418967fa.accept_9_8_6_3_1_457 98 177 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 177 282 (Polychromatic418967fa.accept_9_7_6_3_1_456
  97 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 177 282 3 32 59 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 177 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 95 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 177 282 (Polychromatic418967fa.accept_9_4_6_3_1_179 94 177 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 177 282 3 31 59 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 177 282 (Polychromatic418967fa.accept_9_2_6_3_1_178 92
  177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 177 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 91 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 177 282 3 30 59 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 177 282 (Polychromatic418967fa.accept_9_8_6_3_1_457 89 177 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 177 282 (Polychromatic418967fa.accept_9_7_6_3_1_456
  88 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 177 282 3 29 59 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 177 282
  (Polychromatic418967fa.accept_9_5_6_3_1_40 86 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 177 282 (Polychromatic418967fa.accept_9_4_6_3_1_179 85 177 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 177 282 3 28 59 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 177 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 83
  177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 177 282
  (Polychromatic418967fa.accept_9_1_6_3_1_177 82 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 177 282 3 27 59 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 177 282 (Polychromatic418967fa.accept_9_8_6_3_1_457 80 177 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 177 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 79
  177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 177 282 3 26 59 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 177 282
  (Polychromatic418967fa.accept_9_5_6_3_1_40 77 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 177 282 (Polychromatic418967fa.accept_9_4_6_3_1_179 76 177 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 177 282 3 25 59 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 177 282 (Polychromatic418967fa.accept_9_2_6_3_1_178 74
  177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 177 282
  (Polychromatic418967fa.accept_9_1_6_3_1_177 73 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 177 282 3 24 59 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 177 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 177 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 177 282 (Polychromatic418967fa.accept_9_7_6_3_1_456
  70 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 177 282 3 23 59 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 177 282
  (Polychromatic418967fa.accept_9_5_6_3_1_40 68 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 177 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 177 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 177 282 3 22 59 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 177 282 (Polychromatic418967fa.accept_9_2_6_3_1_178 65
  177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 177 282
  (Polychromatic418967fa.accept_9_1_6_3_1_177 64 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 177 282 3 21 59 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 177 282 (Polychromatic418967fa.accept_9_8_6_3_1_457 62 177 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 177 282 (Polychromatic418967fa.accept_9_7_6_3_1_456
  61 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 177 282 3 20 59 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 177 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 177 282 (Polychromatic418967fa.accept_9_4_6_3_1_179 58 177 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 177 282 3 19 59 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 177 282 (Polychromatic418967fa.accept_9_2_6_3_1_178 56
  177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 177 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 55 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 177 282 3 18 59 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 177 282 (Polychromatic418967fa.accept_9_8_6_3_1_457 53 177 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 177 282 (Polychromatic418967fa.accept_9_7_6_3_1_456
  52 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 177 282 3 17 59 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 177 282
  (Polychromatic418967fa.accept_9_5_6_3_1_40 50 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 177 282 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 177 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 177 282 3 16 59 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 177 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 177 282
  (Polychromatic418967fa.accept_9_1_6_3_1_177 46 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 177 282 3 15 59 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 177 282 (Polychromatic418967fa.accept_9_8_6_3_1_457 44 177 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 177 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 43
  177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 177 282 3 14 59 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 177 282
  (Polychromatic418967fa.accept_9_5_6_3_1_40 41 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 177 282 (Polychromatic418967fa.accept_9_4_6_3_1_179 40 177 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 177 282 3 13 59 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 177 282 (Polychromatic418967fa.accept_9_2_6_3_1_178 38
  177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 282
  (Polychromatic418967fa.accept_9_1_6_3_1_177 37 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 177 282 3 12 59 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 177 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 177 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 177 282 (Polychromatic418967fa.accept_9_7_6_3_1_456
  34 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 177 282 3 11 59 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 177 282
  (Polychromatic418967fa.accept_9_5_6_3_1_40 32 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 177 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 177 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 177 282 3 10 59 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 177 282 (Polychromatic418967fa.accept_9_2_6_3_1_178 29
  177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 177 282
  (Polychromatic418967fa.accept_9_1_6_3_1_177 28 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 177 282 3 9 59 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 177 282 (Polychromatic418967fa.accept_9_8_6_3_1_457 26 177 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 282 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 177 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 177 282 3 8 59 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 177 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 177 282 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 177 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 177 282 3 7 59 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 177 282 (Polychromatic418967fa.accept_9_2_6_3_1_178 20
  177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 177 282 3 6 59 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 177 282 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 177 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 177 282 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 177 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 177 282 3 5 59 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 177 282
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 177 282 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 177 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 177 282 3 4 59 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 177 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 282
  (Polychromatic418967fa.accept_9_1_6_3_1_177 10 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 177 282 3 3 59 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 177 282 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 177 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 177 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 177 282 3 2 59 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 177 282
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 177 282 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 177 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 177 282 3 1 59 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 177 282 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 177 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 282
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 177 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 177
  282))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 176 282 (Eq.refl Bool.true) (allA_succ_of_gcd 106 176 282 2 53 88 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 176 282
  (Polychromatic418967fa.accept_9_6_5_3_1_205 105 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 176 282 2 52 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 176 282 (accept_3_4 103 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 176 282 2 51 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 176 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 101 176 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 176 282 2 50 88 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 176 282
  (Polychromatic418967fa.accept_12_3_8_6_1_895 99 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 176 282 2 49 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 176 282 (accept_3_4 97 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 176 282 2 48 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 176 282 (Polychromatic418967fa.accept_13_4_7_9_1_5260 95 176 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 176 282 2 47 88 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 176 282
  (Polychromatic418967fa.accept_12_9_8_6_1_466 93 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 176 282 2 46 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 176 282 (accept_3_4 91 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 176 282 2 45 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 176 282 (Polychromatic418967fa.accept_9_8_5_3_1_777 89 176 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 176 282 2 44 88 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 176 282
  (Polychromatic418967fa.accept_7_3_1_2_1_247 87 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 176 282 2 43 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 176 282 (accept_3_4 85 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 176 282 2 42 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 176 282 (Polychromatic418967fa.accept_7_6_1_2_1_230 83 176 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 176 282 2 41 88 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 176 282
  (Polychromatic418967fa.accept_10_1_6_2_1_867 81 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 176 282 2 40 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 176 282 (accept_3_4 79 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 176 282 2 39 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 176 282 (Polychromatic418967fa.accept_19_1_5_16_1_2587 77 176 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 176 282 2 38 88 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 176 282
  (Polychromatic418967fa.accept_12_3_8_6_1_895 75 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 176 282 2 37 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 176 282 (accept_3_4 73 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 176 282 2 36 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 176 282 (Polychromatic418967fa.accept_9_8_5_3_1_777 71 176 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 176 282 2 35 88 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 176 282
  (Polychromatic418967fa.accept_7_6_1_2_1_230 69 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 176 282 2 34 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 176 282 (accept_3_4 67 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 176 282 2 33 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 176 282 (Polychromatic418967fa.accept_9_2_5_3_1_37 65 176 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 176 282 2 32 88 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 176 282
  (Polychromatic418967fa.accept_12_3_8_6_1_895 63 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 176 282 2 31 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 176 282 (accept_3_4 61 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 176 282 2 30 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 176 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 176 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 176 282 2 29 88 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 176 282
  (Polychromatic418967fa.accept_12_9_8_6_1_466 57 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 176 282 2 28 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 176 282 (accept_3_4 55 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 176 282 2 27 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 176 282 (Polychromatic418967fa.accept_9_8_5_3_1_777 53 176 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 176 282 2 26 88 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 176 282
  (Polychromatic418967fa.accept_9_6_5_3_1_205 51 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 176 282 2 25 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 176 282 (accept_3_4 49 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 176 282 2 24 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 176 282 (Polychromatic418967fa.accept_9_2_5_3_1_37 47 176 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 176 282 2 23 88 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 176 282
  (Polychromatic418967fa.accept_7_3_1_2_1_247 45 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 176 282 2 22 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 176 282 (accept_3_4 43 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 176 282 2 21 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 176 282 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 176 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 176 282 2 20 88 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 176 282
  (Polychromatic418967fa.accept_12_3_8_6_1_895 39 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 176 282 2 19 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 176 282 (accept_3_4 37 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 176 282 2 18 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 176 282 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 176 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 176 282 2 17 88 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 176 282
  (Polychromatic418967fa.accept_9_6_5_3_1_205 33 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 176 282 2 16 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 176 282 (accept_3_4 31 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 176 282 2 15 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 176 282 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 176 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 176 282 2 14 88 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 176 282
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 176 282 2 13 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 176 282 (accept_3_4 25 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 176 282 2 12 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 176 282 (Polychromatic418967fa.accept_15_8_11_12_1_1626 23 176 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 176 282 2 11 88 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 176 282
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 176 282 2 10 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 176 282 (accept_3_4 19 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 176 282 2 9 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 176 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 176 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 176 282 2 8 88 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 176 282
  (Polychromatic418967fa.accept_9_6_5_3_1_205 15 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 176 282 2 7 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 176 282 (accept_3_4 13 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 176 282 2 6 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 176 282 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 176 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 176 282 2 5 88 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 176 282
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 176 282 2 4 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 176 282 (accept_3_4 7 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 176
  282 2 3 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  176 282 (Polychromatic418967fa.accept_28_5_8_2_1_17315 5 176 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 176 282 2 2 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 176 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 176 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 176 282 2 1 88 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 176 282 (accept_3_4 1 176 282
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176
  282)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 108 175 282 (Eq.refl Bool.true) (allA_succ_of_accept 107 175 282 (accept_3_5 107 175 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 175 282 (Polychromatic418967fa.accept_9_7_4_3_1_204 106 175
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 175 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 105 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 175 282 (accept_3_5 104 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 175 282 (Polychromatic418967fa.accept_10_3_5_2_1_38 103 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 175 282 (Polychromatic418967fa.accept_11_3_10_7_1_129 102 175 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 175 282 (accept_3_5 101 175 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 175 282 (Polychromatic418967fa.accept_9_1_4_3_1_201 100 175
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 175 282
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 99 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 175 282 (accept_3_5 98 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 175 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 175 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 175 282 (Polychromatic418967fa.accept_9_6_4_3_1_203 96 175 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 175 282 (accept_3_5 95 175 282
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 175 282 (Polychromatic418967fa.accept_13_3_6_9_1_1150
  94 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 175 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 93 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 175 282 (accept_3_5 92 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 175 282 (Polychromatic418967fa.accept_9_1_4_3_1_201 91 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 175 282 (Polychromatic418967fa.accept_20_10_15_2_1_3132 90 175 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 175 282 (accept_3_5 89 175 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 175 282 (Polychromatic418967fa.accept_9_7_4_3_1_204 88 175 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 175 282
  (Polychromatic418967fa.accept_9_6_4_3_1_203 87 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 175 282 (accept_3_5 86 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 175 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 175 282 (Polychromatic418967fa.accept_15_9_10_12_1_1625 84 175 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 175 282 (accept_3_5 83 175 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 175 282 (Polychromatic418967fa.accept_9_1_4_3_1_201 82 175 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 175 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 175 282 (accept_3_5 80 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 175 282 (Polychromatic418967fa.accept_9_7_4_3_1_204 79 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 175 282 (Polychromatic418967fa.accept_9_6_4_3_1_203 78 175 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 175 282 (accept_3_5 77 175 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 175 282 (Polychromatic418967fa.accept_21_13_7_9_1_2528 76 175 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 175 282
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 75 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 175 282 (accept_3_5 74 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 175 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 175 282 (Polychromatic418967fa.accept_13_7_6_9_1_1831 72 175 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 175 282 (accept_3_5 71 175 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 175 282 (Polychromatic418967fa.accept_9_7_4_3_1_204 70 175 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 175 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 175 282 (accept_3_5 68 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 175 282 (Polychromatic418967fa.accept_10_7_5_2_1_880 67 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 175 282 (Polychromatic418967fa.accept_13_1_6_9_1_1197 66 175 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 175 282 (accept_3_5 65 175 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 175 282 (Polychromatic418967fa.accept_9_1_4_3_1_201 64 175 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 175 282
  (Polychromatic418967fa.accept_10_3_5_2_1_38 63 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 175 282 (accept_3_5 62 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 175 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 175 282 (Polychromatic418967fa.accept_9_6_4_3_1_203 60 175 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 175 282 (accept_3_5 59 175 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 175 282 (Polychromatic418967fa.accept_10_8_5_2_1_881 58 175 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 175 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 175 282 (accept_3_5 56 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 175 282 (Polychromatic418967fa.accept_9_1_4_3_1_201 55 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 175 282 (Polychromatic418967fa.accept_13_2_6_9_1_2636 54 175 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 175 282 (accept_3_5 53 175 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 175 282 (Polychromatic418967fa.accept_9_7_4_3_1_204 52 175 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 175 282
  (Polychromatic418967fa.accept_9_6_4_3_1_203 51 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 175 282 (accept_3_5 50 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 175 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 175 282 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 175 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 175 282 (accept_3_5 47 175 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 175 282 (Polychromatic418967fa.accept_9_1_4_3_1_201 46 175 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 175 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 175 282 (accept_3_5 44 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 175 282 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 175 282 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 175 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 175 282 (accept_3_5 41 175 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 175 282 (Polychromatic418967fa.accept_13_1_6_9_1_1197 40 175 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 175 282
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 39 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 175 282 (accept_3_5 38 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 175 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 175 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 175 282 (Polychromatic418967fa.accept_11_3_10_7_1_129 36 175
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 175 282 (accept_3_5 35 175
  282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 175 282
  (Polychromatic418967fa.accept_9_7_4_3_1_204 34 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 175 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 175 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 175 282 (accept_3_5 32 175 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 175 282 (Polychromatic418967fa.accept_17_14_5_10_1_9052 31 175 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 175 282
  (Polychromatic418967fa.accept_13_4_6_9_1_3401 30 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 175 282 (accept_3_5 29 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 175 282 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 175 282 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 175 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 175 282 (accept_3_5 26 175 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 175 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 175 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 175 282
  (Polychromatic418967fa.accept_9_6_4_3_1_203 24 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 175 282 (accept_3_5 23 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 175 282 (Polychromatic418967fa.accept_15_7_10_12_1_2403 22 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 175 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 175 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 175 282 (accept_3_5 20 175 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 175 282 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 175 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 175 282
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 175 282 (accept_3_5 17 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 175 282 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 175 282 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 175 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 175 282 (accept_3_5 14 175 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 175 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 175 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 175 282
  (Polychromatic418967fa.accept_14_12_7_2_1_1663 12 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 175 282 (accept_3_5 11 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 175 282 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 175 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 175 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 175 282 (accept_3_5 8 175 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 175 282 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 175 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 175 282
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 175 282 (accept_3_5 5 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  175 282 (Polychromatic418967fa.accept_13_4_6_9_1_3401 4 175 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 175 282 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 175 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 282 (accept_3_5 2 175 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 175 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 175 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175
  282))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 109 174 282 (Eq.refl Bool.true) (allA_succ_of_gcd 108 174 282 6 18 29 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 174 282
  (Polychromatic418967fa.accept_10_7_4_2_1_903 107 174 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 174 282 2 53 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 105 174 282 3 35 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 104 174 282 2 52 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 174 282 (Polychromatic418967fa.accept_16_7_14_10_1_3544 103
  174 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 174 282 6 17 29 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 174 282
  (Polychromatic418967fa.accept_7_3_6_2_1_90 101 174 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 174 282 2 50 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 99 174 282 3 33 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 98 174 282 2 49 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 174 282 (Polychromatic418967fa.accept_10_7_4_2_1_903 97 174 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 174 282 6 16 29 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 174 282
  (Polychromatic418967fa.accept_7_4_6_2_1_451 95 174 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 174 282 2 47 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 93 174 282 3 31 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 92 174 282 2 46 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 174 282 (Polychromatic418967fa.accept_17_6_4_10_1_5176 91 174
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 174 282 6 15 29 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 174 282
  (Polychromatic418967fa.accept_15_14_9_12_1_2498 89 174 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 174 282 2 44 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 87 174 282 3 29 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 174 282 2 43 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 174 282 (Polychromatic418967fa.accept_7_1_6_2_1_18 85
  174 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 174 282 6 14 29 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 174 282
  (Polychromatic418967fa.accept_17_15_4_10_1_3968 83 174 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 174 282 2 41 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 81 174 282 3 27 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 174 282 2 40 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 174 282 (Polychromatic418967fa.accept_11_2_9_7_1_124
  79 174 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 174 282 6 13 29 47
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 174 282
  (Polychromatic418967fa.accept_10_7_4_2_1_903 77 174 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 174 282 2 38 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 174 282 3 25 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 174 282 2 37 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 174 282 (Polychromatic418967fa.accept_7_3_6_2_1_90 73 174 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 174 282 6 12 29 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 174 282
  (Polychromatic418967fa.accept_7_1_6_2_1_18 71 174 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 174 282 2 35 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 174 282 3 23 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 174 282 2 34 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 174 282 (Polychromatic418967fa.accept_7_4_6_2_1_451 67 174 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 174 282 6 11 29 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 174 282
  (Polychromatic418967fa.accept_15_5_9_12_1_1599 65 174 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 174 282 2 32 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 174 282 3 21 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 62 174 282 2 31 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 174 282 (Polychromatic418967fa.accept_16_13_14_10_1_1669 61 174
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 174 282 6 10 29 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 174 282
  (Polychromatic418967fa.accept_7_3_6_2_1_90 59 174 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 174 282 2 29 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 57 174 282 3 19 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 56 174 282 2 28 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 174 282 (Polychromatic418967fa.accept_13_3_5_9_1_5285 55 174
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 174 282 6 9 29 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 174 282
  (Polychromatic418967fa.accept_7_4_6_2_1_451 53 174 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 174 282 2 26 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 174 282 3 17 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 174 282 2 25 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 174 282 (Polychromatic418967fa.accept_11_5_9_7_1_411 49 174 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 174 282 6 8 29 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 174 282
  (Polychromatic418967fa.accept_10_7_4_2_1_903 47 174 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 174 282 2 23 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 174 282 3 15 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 174 282 2 22 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 174 282 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 174 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 174 282 6 7 29 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 174 282
  (Polychromatic418967fa.accept_13_2_5_9_1_610 41 174 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 174 282 2 20 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 174 282 3 13 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 174 282 2 19 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 174 282 (Polychromatic418967fa.accept_10_7_4_2_1_903 37 174 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 174 282 6 6 29 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 174 282
  (Polychromatic418967fa.accept_11_2_9_7_1_124 35 174 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 174 282 2 17 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 174 282 3 11 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 174 282 2 16 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 174 282 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 174 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 174 282 6 5 29 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 174 282
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 174 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 174 282 2 14 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 174 282 3 9 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 174 282 2 13 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 174 282 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 174 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 174 282 6 4 29 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 174 282
  (Polychromatic418967fa.accept_16_7_14_10_1_3544 23 174 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 174 282 2 11 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 21 174 282 3 7 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 20 174 282 2 10 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 174 282 (Polychromatic418967fa.accept_15_4_9_12_1_2495 19 174
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 174 282 6 3 29 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 174 282
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 174 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 174 282 2 8 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 174 282 3 5 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 174 282 2 7 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 174 282 (Polychromatic418967fa.accept_11_2_9_7_1_124 13 174 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 174 282 6 2 29 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 174 282
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 174 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 174 282 2 5 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 174 282 3 3 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 174 282 2 4 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 174 282 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 174 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174 282 6 1 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 174 282 (Polychromatic418967fa.accept_11_5_9_7_1_411 5
  174 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 174 282 2 2 87 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 174 282 3 1 58 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 174 282 2 1 87 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 174 282
  (Polychromatic418967fa.accept_7_1_6_2_1_18 1 174 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 174
  282)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 173 282 (Eq.refl Bool.true) (allA_succ_of_accept 109 173 282 (accept_3_4 109 173 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 173 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 108 173
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 173 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 107 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 173 282 (accept_3_4 106 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 173 282 (Polychromatic418967fa.accept_9_6_2_3_1_771 105 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 173 282 (Polychromatic418967fa.accept_9_5_2_3_1_194 104 173 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 173 282 (accept_3_4 103 173 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 173 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 102 173
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 173 282
  (Polychromatic418967fa.accept_7_3_5_2_1_17 101 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 173 282 (accept_3_4 100 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 173 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 173 282 (Polychromatic418967fa.accept_9_8_2_3_1_447 98 173 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 173 282 (accept_3_4 97 173 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 173 282 (Polychromatic418967fa.accept_9_6_2_3_1_771 96 173 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 173 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 95 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 173 282 (accept_3_4 94 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 173 282 (Polychromatic418967fa.accept_15_3_8_12_1_900 93 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 173 282 (Polychromatic418967fa.accept_11_4_8_7_1_819 92 173 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 173 282 (accept_3_4 91 173 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 173 282 (Polychromatic418967fa.accept_19_14_2_16_1_6484 90 173
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 173 282
  (Polychromatic418967fa.accept_9_8_2_3_1_447 89 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 173 282 (accept_3_4 88 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 173 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 173 282 (Polychromatic418967fa.accept_9_5_2_3_1_194 86 173 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 173 282 (accept_3_4 85 173 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 173 282 (Polychromatic418967fa.accept_13_6_4_9_1_4326 84 173 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 173 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 173 282 (accept_3_4 82 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 173 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 81 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 173 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 80 173 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 173 282 (accept_3_4 79 173 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 173 282 (Polychromatic418967fa.accept_9_6_2_3_1_771 78 173 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 173 282
  (Polychromatic418967fa.accept_9_5_2_3_1_194 77 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 173 282 (accept_3_4 76 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 173 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 173 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 74 173 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 173 282 (accept_3_4 73 173 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 173 282 (Polychromatic418967fa.accept_13_7_4_9_1_1865 72 173 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 173 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 173 282 (accept_3_4 70 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 173 282 (Polychromatic418967fa.accept_9_6_2_3_1_771 69 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 173 282 (Polychromatic418967fa.accept_9_5_2_3_1_194 68 173 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 173 282 (accept_3_4 67 173 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 173 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 173 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 173 282
  (Polychromatic418967fa.accept_10_5_3_2_1_899 65 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 173 282 (accept_3_4 64 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 173 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 173 282 (Polychromatic418967fa.accept_9_8_2_3_1_447 62 173 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 173 282 (accept_3_4 61 173 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 173 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 173 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 173 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 173 282 (accept_3_4 58 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 173 282 (Polychromatic418967fa.accept_13_5_4_9_1_601 57 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 173 282 (Polychromatic418967fa.accept_15_11_8_12_1_4437 56 173 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 173 282 (accept_3_4 55 173 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 173 282 (Polychromatic418967fa.accept_21_12_5_9_1_8504 54 173
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 173 282
  (Polychromatic418967fa.accept_7_4_5_2_1_243 53 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 173 282 (accept_3_4 52 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 173 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 173 282 (Polychromatic418967fa.accept_9_5_2_3_1_194 50 173 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 173 282 (accept_3_4 49 173 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 173 282 (Polychromatic418967fa.accept_11_4_8_7_1_819 48 173 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 173 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 173 282 (accept_3_4 46 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 173 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 173 282 (Polychromatic418967fa.accept_9_8_2_3_1_447 44 173 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 173 282 (accept_3_4 43 173 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 173 282 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 173 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 173 282
  (Polychromatic418967fa.accept_9_5_2_3_1_194 41 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 173 282 (accept_3_4 40 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 173 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 173 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 173 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 173 282 (accept_3_4 37 173 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 173 282 (Polychromatic418967fa.accept_19_17_2_16_1_7982 36 173 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 173 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 173 282 (accept_3_4 34 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 173 282 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 173 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 173 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 173 282 (accept_3_4 31 173 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 173 282 (Polychromatic418967fa.accept_16_14_13_10_1_2624 30 173 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 173 282
  (Polychromatic418967fa.accept_20_9_13_2_1_8908 29 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 173 282 (accept_3_4 28 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 173 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 173 282 (Polychromatic418967fa.accept_9_8_2_3_1_447 26 173 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 173 282 (accept_3_4 25 173 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 173 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 173 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 173 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 173 282 (accept_3_4 22 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 173 282 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 173 282 (Polychromatic418967fa.accept_13_7_4_9_1_1865 20 173 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 173 282 (accept_3_4 19 173 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 173 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 173 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 173 282
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 173 282 (accept_3_4 16 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 173 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 173 282 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 173 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 173 282 (accept_3_4 13 173 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 173 282 (Polychromatic418967fa.accept_16_12_13_10_1_2637 12 173 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 173 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 173 282 (accept_3_4 10 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  173 282 (Polychromatic418967fa.accept_17_9_3_10_1_9070 9 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 173 282 (Polychromatic418967fa.accept_9_8_2_3_1_447 8 173 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 173 282 (accept_3_4 7 173 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 173 282 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 173 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 173 282
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 173 282 (accept_3_4 4 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  173 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 173 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 173 282 (Polychromatic418967fa.accept_23_2_12_6_1_17314 2 173 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 173 282 (accept_3_4 1 173 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 173
  282))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 111 172 282 (Eq.refl Bool.true) (allA_succ_of_gcd 110 172 282 2 55 86 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 172 282
  (Polychromatic418967fa.accept_13_5_3_9_1_1189 109 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 172 282 2 54 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 172 282 (accept_3_5 107 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 172 282 2 53 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 172 282 (Polychromatic418967fa.accept_9_6_1_3_1_191 105 172 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 172 282 2 52 86 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 172 282
  (Polychromatic418967fa.accept_7_5_4_2_1_235 103 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 172 282 2 51 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 172 282 (accept_3_5 101 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 172 282 2 50 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 172 282 (Polychromatic418967fa.accept_12_3_4_6_1_434 99 172 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 172 282 2 49 86 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 172 282
  (Polychromatic418967fa.accept_7_6_4_2_1_236 97 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 172 282 2 48 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 172 282 (accept_3_5 95 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 172 282 2 47 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 172 282 (Polychromatic418967fa.accept_12_9_4_6_1_460 93 172 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 172 282 2 46 86 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 172 282
  (Polychromatic418967fa.accept_16_11_12_10_1_3641 91 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 172 282 2 45 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 172 282 (accept_3_5 89 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 172 282 2 44 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 172 282 (Polychromatic418967fa.accept_9_6_1_3_1_191 87 172 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 172 282 2 43 86 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 172 282
  (Polychromatic418967fa.accept_9_4_1_3_1_190 85 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 172 282 2 42 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 172 282 (accept_3_5 83 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 172 282 2 41 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 172 282 (Polychromatic418967fa.accept_12_9_4_6_1_460 81 172 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 172 282 2 40 86 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 172 282
  (Polychromatic418967fa.accept_9_7_1_3_1_443 79 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 172 282 2 39 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 172 282 (accept_3_5 77 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 172 282 2 38 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 172 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 75 172 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 172 282 2 37 86 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 172 282
  (Polychromatic418967fa.accept_13_8_3_9_1_5269 73 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 172 282 2 36 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 172 282 (accept_3_5 71 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 172 282 2 35 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 172 282 (Polychromatic418967fa.accept_7_6_4_2_1_236 69 172 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 172 282 2 34 86 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 172 282
  (Polychromatic418967fa.accept_9_4_1_3_1_190 67 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 172 282 2 33 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 172 282 (accept_3_5 65 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 172 282 2 32 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 172 282 (Polychromatic418967fa.accept_12_3_4_6_1_434 63 172 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 172 282 2 31 86 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 172 282
  (Polychromatic418967fa.accept_7_5_4_2_1_235 61 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 172 282 2 30 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 172 282 (accept_3_5 59 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 172 282 2 29 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 172 282 (Polychromatic418967fa.accept_12_9_4_6_1_460 57 172 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 172 282 2 28 86 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 172 282
  (Polychromatic418967fa.accept_7_6_4_2_1_236 55 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 172 282 2 27 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 172 282 (accept_3_5 53 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 172 282 2 26 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 172 282 (Polychromatic418967fa.accept_9_6_1_3_1_191 51 172 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 172 282 2 25 86 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 172 282
  (Polychromatic418967fa.accept_9_4_1_3_1_190 49 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 172 282 2 24 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 172 282 (accept_3_5 47 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 172 282 2 23 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 172 282 (Polychromatic418967fa.accept_12_9_4_6_1_460 45 172 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 172 282 2 22 86 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 172 282
  (Polychromatic418967fa.accept_9_7_1_3_1_443 43 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 172 282 2 21 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 172 282 (accept_3_5 41 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 172 282 2 20 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 172 282 (Polychromatic418967fa.accept_12_3_4_6_1_434 39 172 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 172 282 2 19 86 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 172 282
  (Polychromatic418967fa.accept_14_9_4_2_1_983 37 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 172 282 2 18 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 172 282 (accept_3_5 35 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 172 282 2 17 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 172 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 172 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 172 282 2 16 86 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 172 282
  (Polychromatic418967fa.accept_9_4_1_3_1_190 31 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 172 282 2 15 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 172 282 (accept_3_5 29 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 172 282 2 14 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 172 282 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 172 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 172 282 2 13 86 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 172 282
  (Polychromatic418967fa.accept_9_7_1_3_1_443 25 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 172 282 2 12 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 172 282 (accept_3_5 23 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 172 282 2 11 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 172 282 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 172 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 172 282 2 10 86 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 172 282
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 172 282 2 9 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 172 282 (accept_3_5 17 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 172 282 2 8 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 172 282 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 172 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 172 282 2 7 86 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 172 282
  (Polychromatic418967fa.accept_7_6_4_2_1_236 13 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 172 282 2 6 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 172 282 (accept_3_5 11 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 172 282 2 5 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 172 282 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 172 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 172 282 2 4 86 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 172 282
  (Polychromatic418967fa.accept_9_7_1_3_1_443 7 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 172 282 2 3 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 172 282 (accept_3_5 5 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 172
  282 2 2 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  172 282 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 172 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 172 282 2 1 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 172 282 (Polychromatic418967fa.accept_23_1_11_6_1_17313 1 172 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 172
  282)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 112 171 282 (Eq.refl Bool.true) (allA_succ_of_gcd 111 171 282 3 37 57 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 110 171 282
  (Polychromatic418967fa.accept_7_5_3_2_1_249 110 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 171 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 109 171 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 171 282 3 36 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 171 282 (Polychromatic418967fa.accept_13_3_2_9_1_1187
  107 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 171 282
  (Polychromatic418967fa.accept_7_1_3_2_1_13 106 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 171 282 3 35 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 171 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 104 171 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 171 282
  (Polychromatic418967fa.accept_7_5_3_2_1_249 103 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 171 282 3 34 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 171 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 101 171 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 171 282 (Polychromatic418967fa.accept_11_1_6_7_1_116
  100 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 171 282 3 33 57 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 171 282
  (Polychromatic418967fa.accept_12_2_3_6_1_112 98 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 171 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 171 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 171 282 3 32 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 171 282 (Polychromatic418967fa.accept_15_5_6_12_1_916
  95 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 171 282
  (Polychromatic418967fa.accept_12_10_3_6_1_882 94 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 171 282 3 31 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 171 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 92 171 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 171 282 (Polychromatic418967fa.accept_21_7_3_9_1_5294
  91 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 171 282 3 30 57 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 171 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 171 282 (Polychromatic418967fa.accept_12_4_3_6_1_879 88 171 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 171 282 3 29 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 171 282 (Polychromatic418967fa.accept_10_6_1_2_1_874
  86 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 171 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 85 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 171 282 3 28 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 171 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 83 171 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 171 282 (Polychromatic418967fa.accept_7_5_3_2_1_249
  82 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 171 282 3 27 57 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 171 282
  (Polychromatic418967fa.accept_12_8_3_6_1_909 80 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 171 282 (Polychromatic418967fa.accept_10_9_1_2_1_522 79 171 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 171 282 3 26 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 171 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 77
  171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 171 282
  (Polychromatic418967fa.accept_7_6_3_2_1_461 76 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 171 282 3 25 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 171 282 (Polychromatic418967fa.accept_12_2_3_6_1_112 74 171 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 171 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 73
  171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 171 282 3 24 57 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 171 282
  (Polychromatic418967fa.accept_7_1_3_2_1_13 71 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 171 282 (Polychromatic418967fa.accept_12_10_3_6_1_882 70 171 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 171 282 3 23 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 171 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 68
  171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 171 282
  (Polychromatic418967fa.accept_11_1_6_7_1_116 67 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 171 282 3 22 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 171 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 171 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 171 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 64
  171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 171 282 3 21 57 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 171 282
  (Polychromatic418967fa.accept_7_6_3_2_1_461 62 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 171 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 171 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 171 282 3 20 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 171 282 (Polychromatic418967fa.accept_10_9_1_2_1_522
  59 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 171 282
  (Polychromatic418967fa.accept_12_10_3_6_1_882 58 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 171 282 3 19 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 171 282 (Polychromatic418967fa.accept_10_6_1_2_1_874 56 171 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 171 282 (Polychromatic418967fa.accept_7_6_3_2_1_461
  55 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 171 282 3 18 57 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 171 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 171 282 (Polychromatic418967fa.accept_12_4_3_6_1_879 52 171 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 171 282 3 17 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 171 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 50
  171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 171 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 171 282 3 16 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 171 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 171 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 171 282 (Polychromatic418967fa.accept_10_6_1_2_1_874
  46 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 171 282 3 15 57 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 171 282
  (Polychromatic418967fa.accept_12_8_3_6_1_909 44 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 171 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 171 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 171 282 3 14 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 171 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 41
  171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 171 282
  (Polychromatic418967fa.accept_7_5_3_2_1_249 40 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 171 282 3 13 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 171 282 (Polychromatic418967fa.accept_12_2_3_6_1_112 38 171 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 37
  171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 171 282 3 12 57 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 171 282
  (Polychromatic418967fa.accept_15_5_6_12_1_916 35 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 171 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 171 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 171 282 3 11 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 171 282 (Polychromatic418967fa.accept_12_8_3_6_1_909
  32 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 282
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 31 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 171 282 3 10 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 171 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 171 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 171 282 (Polychromatic418967fa.accept_12_4_3_6_1_879
  28 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 171 282 3 9 57 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 171 282
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 171 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 171 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 171 282 3 8 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 171 282 (Polychromatic418967fa.accept_10_3_1_2_1_521
  23 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 171 282
  (Polychromatic418967fa.accept_7_1_3_2_1_13 22 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 171 282 3 7 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 171 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 171 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 171 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 171 282 3 6 57 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 171 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 171 282 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 171 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 171 282 3 5 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 171 282 (Polychromatic418967fa.accept_12_2_3_6_1_112
  14 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 171 282 3 4 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 171 282 (Polychromatic418967fa.accept_13_11_2_9_1_2640 11 171 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 171 282 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 171
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 171 282 3 3 57 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 171 282
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 171 282 (Polychromatic418967fa.accept_13_7_2_9_1_1826 7 171 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 171 282 3 2 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 171 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 171 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 282
  (Polychromatic418967fa.accept_12_4_3_6_1_879 4 171 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 171 282 3 1 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 171 282 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 171 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 171 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 171
  282))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 113 170 282 (Eq.refl Bool.true) (allA_succ_of_gcd 112 170 282 2 56 85 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 170 282
  (Polychromatic418967fa.accept_12_3_2_6_1_138 111 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 170 282 2 55 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 170 282 (accept_3_4 109 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 170 282 2 54 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 170 282 (Polychromatic418967fa.accept_15_2_5_12_1_369 107 170 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 170 282 2 53 85 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 170 282
  (Polychromatic418967fa.accept_9_6_8_3_1_183 105 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 170 282 2 52 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 170 282 (accept_3_4 103 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 170 282 2 51 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 170 282 (Polychromatic418967fa.accept_9_2_8_3_1_181 101 170 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 170 282 2 50 85 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 170 282
  (Polychromatic418967fa.accept_12_3_2_6_1_138 99 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 170 282 2 49 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 170 282 (accept_3_4 97 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 170 282 2 48 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 170 282 (Polychromatic418967fa.accept_9_5_8_3_1_437 95 170 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 170 282 2 47 85 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 170 282
  (Polychromatic418967fa.accept_12_9_2_6_1_455 93 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 170 282 2 46 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 170 282 (accept_3_4 91 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 170 282 2 45 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 170 282 (Polychromatic418967fa.accept_13_11_1_9_1_1179 89 170 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 170 282 2 44 85 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 170 282
  (Polychromatic418967fa.accept_9_6_8_3_1_183 87 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 170 282 2 43 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 170 282 (accept_3_4 85 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 170 282 2 42 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 170 282 (Polychromatic418967fa.accept_9_2_8_3_1_181 83 170 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 170 282 2 41 85 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 170 282
  (Polychromatic418967fa.accept_12_9_2_6_1_455 81 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 170 282 2 40 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 170 282 (accept_3_4 79 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 170 282 2 39 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 170 282 (Polychromatic418967fa.accept_9_5_8_3_1_437 77 170 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 170 282 2 38 85 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 170 282
  (Polychromatic418967fa.accept_11_9_5_7_1_815 75 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 170 282 2 37 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 170 282 (accept_3_4 73 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 170 282 2 36 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 170 282 (Polychromatic418967fa.accept_13_6_1_9_1_619 71 170 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 170 282 2 35 85 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 170 282
  (Polychromatic418967fa.accept_9_6_8_3_1_183 69 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 170 282 2 34 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 170 282 (accept_3_4 67 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 170 282 2 33 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 170 282 (Polychromatic418967fa.accept_9_2_8_3_1_181 65 170 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 170 282 2 32 85 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 170 282
  (Polychromatic418967fa.accept_12_3_2_6_1_138 63 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 170 282 2 31 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 170 282 (accept_3_4 61 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 170 282 2 30 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 170 282 (Polychromatic418967fa.accept_9_5_8_3_1_437 59 170 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 170 282 2 29 85 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 170 282
  (Polychromatic418967fa.accept_12_9_2_6_1_455 57 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 170 282 2 28 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 170 282 (accept_3_4 55 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 170 282 2 27 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 170 282 (Polychromatic418967fa.accept_11_9_5_7_1_815 53 170 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 170 282 2 26 85 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 170 282
  (Polychromatic418967fa.accept_9_6_8_3_1_183 51 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 170 282 2 25 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 170 282 (accept_3_4 49 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 170 282 2 24 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 170 282 (Polychromatic418967fa.accept_9_2_8_3_1_181 47 170 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 170 282 2 23 85 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 170 282
  (Polychromatic418967fa.accept_12_9_2_6_1_455 45 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 170 282 2 22 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 170 282 (accept_3_4 43 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 170 282 2 21 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 170 282 (Polychromatic418967fa.accept_9_5_8_3_1_437 41 170 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 170 282 2 20 85 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 170 282
  (Polychromatic418967fa.accept_12_3_2_6_1_138 39 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 170 282 2 19 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 170 282 (accept_3_4 37 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 170 282 2 18 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 170 282 (Polychromatic418967fa.accept_20_15_10_2_1_5924 35 170 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 170 282 2 17 85 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 170 282
  (Polychromatic418967fa.accept_9_6_8_3_1_183 33 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 170 282 2 16 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 170 282 (accept_3_4 31 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 170 282 2 15 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 170 282 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 170 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 170 282 2 14 85 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 170 282
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 170 282 2 13 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 170 282 (accept_3_4 25 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 170 282 2 12 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 170 282 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 170 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 170 282 2 11 85 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 170 282
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 170 282 2 10 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 170 282 (accept_3_4 19 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 170 282 2 9 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 170 282 (Polychromatic418967fa.accept_15_2_5_12_1_369 17 170 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 170 282 2 8 85 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 170 282
  (Polychromatic418967fa.accept_9_6_8_3_1_183 15 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 170 282 2 7 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 170 282 (accept_3_4 13 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 170 282 2 6 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 170 282 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 170 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 170 282 2 5 85 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 170 282
  (Polychromatic418967fa.accept_11_9_5_7_1_815 9 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 170 282 2 4 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 170 282 (accept_3_4 7 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 170
  282 2 3 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  170 282 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 170 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 170 282 2 2 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 170 282 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 170 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 170 282 2 1 85 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 170 282 (accept_3_4 1 170 282
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  282)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 114 169 282 (Eq.refl Bool.true) (allA_succ_of_accept 113 169 282 (accept_3_5 113 169 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 169 282 (Polychromatic418967fa.accept_9_4_7_3_1_43 112 169
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 169 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 111 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 169 282 (accept_3_5 110 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 169 282 (Polychromatic418967fa.accept_9_1_7_3_1_41 109 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 169 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 108 169 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 169 282 (accept_3_5 107 169 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 169 282 (Polychromatic418967fa.accept_14_8_1_2_1_965 106 169
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 169 282
  (Polychromatic418967fa.accept_9_6_7_3_1_436 105 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 169 282 (accept_3_5 104 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 169 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 103 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 169 282 (Polychromatic418967fa.accept_11_3_4_7_1_114 102 169 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 169 282 (accept_3_5 101 169 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 169 282 (Polychromatic418967fa.accept_9_1_7_3_1_41 100 169
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 169 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 99 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 169 282 (accept_3_5 98 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 169 282 (Polychromatic418967fa.accept_7_6_1_2_1_230 97 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 169 282 (Polychromatic418967fa.accept_9_6_7_3_1_436 96 169 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 169 282 (accept_3_5 95 169 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 169 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 94 169 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 169 282
  (Polychromatic418967fa.accept_18_3_7_12_1_1196 93 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 169 282 (accept_3_5 92 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 169 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 169 282 (Polychromatic418967fa.accept_7_6_1_2_1_230 90 169 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 169 282 (accept_3_5 89 169 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 169 282 (Polychromatic418967fa.accept_25_13_19_7_1_6688 88 169 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 169 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 87 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 169 282 (accept_3_5 86 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 169 282 (Polychromatic418967fa.accept_9_4_7_3_1_43 85 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 169 282 (Polychromatic418967fa.accept_15_9_4_12_1_1611 84 169 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 169 282 (accept_3_5 83 169 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 169 282 (Polychromatic418967fa.accept_9_1_7_3_1_41 82 169 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 169 282
  (Polychromatic418967fa.accept_10_1_9_2_1_45 81 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 169 282 (accept_3_5 80 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 169 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 169 282 (Polychromatic418967fa.accept_9_6_7_3_1_436 78 169 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 169 282 (accept_3_5 77 169 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 169 282 (Polychromatic418967fa.accept_7_6_1_2_1_230 76 169 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 169 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 169 282 (accept_3_5 74 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 169 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 73 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 169 282 (Polychromatic418967fa.accept_20_12_9_2_1_4472 72 169 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 169 282 (accept_3_5 71 169 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 169 282 (Polychromatic418967fa.accept_19_13_17_16_1_6479 70
  169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 169 282
  (Polychromatic418967fa.accept_7_6_1_2_1_230 69 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 169 282 (accept_3_5 68 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 169 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 169 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 169 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 169 282 (accept_3_5 65 169 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 169 282 (Polychromatic418967fa.accept_9_1_7_3_1_41 64 169 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 169 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 169 282 (accept_3_5 62 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 169 282 (Polychromatic418967fa.accept_10_1_9_2_1_45 61 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 169 282 (Polychromatic418967fa.accept_9_6_7_3_1_436 60 169 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 169 282 (accept_3_5 59 169 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 169 282 (Polychromatic418967fa.accept_9_4_7_3_1_43 58 169 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 169 282
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 57 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 169 282 (accept_3_5 56 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 169 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 169 282 (Polychromatic418967fa.accept_15_9_4_12_1_1611 54 169 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 169 282 (accept_3_5 53 169 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 169 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 52 169 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 169 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 169 282 (accept_3_5 50 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 169 282 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 169 282 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 169 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 169 282 (accept_3_5 47 169 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 169 282 (Polychromatic418967fa.accept_9_1_7_3_1_41 46 169 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 169 282
  (Polychromatic418967fa.accept_7_3_1_2_1_247 45 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 169 282 (accept_3_5 44 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 169 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 169 282 (Polychromatic418967fa.accept_9_6_7_3_1_436 42 169 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 169 282 (accept_3_5 41 169 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 169 282 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 169 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 169 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 169 282 (accept_3_5 38 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 169 282 (Polychromatic418967fa.accept_9_1_7_3_1_41 37 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 169 282 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 169 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 169 282 (accept_3_5 35 169 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 169 282 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 169 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 169 282
  (Polychromatic418967fa.accept_9_6_7_3_1_436 33 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 169 282 (accept_3_5 32 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 169 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 169 282 (Polychromatic418967fa.accept_11_8_4_7_1_1303 30 169 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 169 282 (accept_3_5 29 169 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 169 282 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 169 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 169 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 169 282 (accept_3_5 26 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 169 282 (Polychromatic418967fa.accept_11_3_4_7_1_114 25 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 169 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 169 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 169 282 (accept_3_5 23 169 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 169 282 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 169 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 169 282
  (Polychromatic418967fa.accept_10_1_9_2_1_45 21 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 169 282 (accept_3_5 20 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 169 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 169 282 (Polychromatic418967fa.accept_19_18_17_16_1_6494 18 169 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 169 282 (accept_3_5 17 169 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 169 282 (Polychromatic418967fa.accept_15_1_4_12_1_2401 16 169
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 169 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 169 282 (accept_3_5 14 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 169 282 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 169 282 (Polychromatic418967fa.accept_20_12_9_2_1_4472 12 169 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 169 282 (accept_3_5 11 169 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 169 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 169 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 169 282
  (Polychromatic418967fa.accept_15_9_4_12_1_1611 9 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 169 282 (accept_3_5 8 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  169 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 169 282 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 169 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 169 282 (accept_3_5 5 169 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 169 282 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 169 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 282 (accept_3_5 2 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 282 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 169 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169
  282))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 115 168 282 (Eq.refl Bool.true) (allA_succ_of_gcd 114 168 282 6 19 28 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 168 282
  (Polychromatic418967fa.accept_9_5_6_3_1_40 113 168 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 168 282 2 56 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 111 168 282 3 37 56 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 110 168 282 2 55 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 168 282 (Polychromatic418967fa.accept_9_1_6_3_1_177 109 168
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 168 282 6 18 28 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 168 282
  (Polychromatic418967fa.accept_9_8_6_3_1_457 107 168 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 168 282 2 53 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 105 168 282 3 35 56 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 104 168 282 2 52 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 168 282 (Polychromatic418967fa.accept_9_4_6_3_1_179 103 168
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 168 282 6 17 28 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 168 282
  (Polychromatic418967fa.accept_9_2_6_3_1_178 101 168 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 168 282 2 50 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 99 168 282 3 33 56 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 98 168 282 2 49 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 168 282 (Polychromatic418967fa.accept_9_7_6_3_1_456 97 168 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 168 282 6 16 28 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 168 282
  (Polychromatic418967fa.accept_9_5_6_3_1_40 95 168 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 168 282 2 47 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 93 168 282 3 31 56 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 92 168 282 2 46 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 168 282 (Polychromatic418967fa.accept_9_1_6_3_1_177 91 168 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 168 282 6 15 28 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 168 282
  (Polychromatic418967fa.accept_9_8_6_3_1_457 89 168 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 168 282 2 44 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 87 168 282 3 29 56 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 86 168 282 2 43 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 168 282 (Polychromatic418967fa.accept_9_4_6_3_1_179 85 168 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 168 282 6 14 28 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 168 282
  (Polychromatic418967fa.accept_9_2_6_3_1_178 83 168 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 168 282 2 41 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 168 282 3 27 56 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 80 168 282 2 40 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 168 282 (Polychromatic418967fa.accept_9_7_6_3_1_456 79 168 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 168 282 6 13 28 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 168 282
  (Polychromatic418967fa.accept_9_5_6_3_1_40 77 168 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 168 282 2 38 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 168 282 3 25 56 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 168 282 2 37 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 168 282 (Polychromatic418967fa.accept_9_1_6_3_1_177 73 168 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 168 282 6 12 28 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 168 282
  (Polychromatic418967fa.accept_9_8_6_3_1_457 71 168 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 168 282 2 35 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 168 282 3 23 56 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 168 282 2 34 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 168 282 (Polychromatic418967fa.accept_9_4_6_3_1_179 67 168 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 168 282 6 11 28 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 168 282
  (Polychromatic418967fa.accept_9_2_6_3_1_178 65 168 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 168 282 2 32 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 168 282 3 21 56 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 62 168 282 2 31 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 168 282 (Polychromatic418967fa.accept_9_7_6_3_1_456 61 168 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 168 282 6 10 28 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 168 282
  (Polychromatic418967fa.accept_9_5_6_3_1_40 59 168 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 168 282 2 29 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 57 168 282 3 19 56 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 56 168 282 2 28 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 168 282 (Polychromatic418967fa.accept_9_1_6_3_1_177 55 168 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 168 282 6 9 28 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 168 282
  (Polychromatic418967fa.accept_9_8_6_3_1_457 53 168 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 168 282 2 26 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 168 282 3 17 56 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 168 282 2 25 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 168 282 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 168 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 168 282 6 8 28 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 168 282
  (Polychromatic418967fa.accept_9_2_6_3_1_178 47 168 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 168 282 2 23 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 168 282 3 15 56 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 168 282 2 22 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 168 282 (Polychromatic418967fa.accept_9_7_6_3_1_456 43 168 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 168 282 6 7 28 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 168 282
  (Polychromatic418967fa.accept_9_5_6_3_1_40 41 168 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 168 282 2 20 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 168 282 3 13 56 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 168 282 2 19 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 168 282 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 168 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 168 282 6 6 28 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 168 282
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 168 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 168 282 2 17 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 168 282 3 11 56 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 168 282 2 16 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 168 282 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 168 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 168 282 6 5 28 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 168 282
  (Polychromatic418967fa.accept_9_2_6_3_1_178 29 168 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 168 282 2 14 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 168 282 3 9 56 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 168 282 2 13 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 168 282 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 168 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 168 282 6 4 28 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 168 282
  (Polychromatic418967fa.accept_9_5_6_3_1_40 23 168 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 168 282 2 11 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 168 282 3 7 56 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 168 282 2 10 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 168 282 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 168 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 168 282 6 3 28 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 168 282
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 168 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 168 282 2 8 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 168 282 3 5 56 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 168 282 2 7 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 168 282 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 168 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 168 282 6 2 28 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 168 282
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 168 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 168 282 2 5 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 168 282 3 3 56 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 168 282 2 4 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 168 282 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 168 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168 282 6 1 28 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 168 282 (Polychromatic418967fa.accept_9_5_6_3_1_40 5
  168 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 168 282 2 2 84 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 168 282 3 1 56 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 168 282 2 1 84 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 282
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 168 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 168
  282)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 116 167 282 (Eq.refl Bool.true) (allA_succ_of_accept 115 167 282 (accept_3_4 115 167 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 167 282 (Polychromatic418967fa.accept_9_6_5_3_1_205 114 167
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 167 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 113 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 167 282 (accept_3_4 112 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 167 282 (Polychromatic418967fa.accept_13_7_11_9_1_1858 111 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 110 167 282 (Polychromatic418967fa.accept_9_2_5_3_1_37 110 167 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 167 282 (accept_3_4 109 167 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 167 282 (Polychromatic418967fa.accept_7_3_6_2_1_90 108 167
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 167 282
  (Polychromatic418967fa.accept_9_8_5_3_1_777 107 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 167 282 (accept_3_4 106 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 167 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 105 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 167 282 (Polychromatic418967fa.accept_10_4_7_2_1_211 104 167 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 167 282 (accept_3_4 103 167 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 167 282 (Polychromatic418967fa.accept_7_4_6_2_1_451 102 167
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 167 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 101 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 167 282 (accept_3_4 100 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 167 282 (Polychromatic418967fa.accept_7_1_6_2_1_18 99 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 167 282 (Polychromatic418967fa.accept_9_8_5_3_1_777 98 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 167 282 (accept_3_4 97 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 167 282 (Polychromatic418967fa.accept_9_6_5_3_1_205 96 167 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 167 282
  (Polychromatic418967fa.accept_7_4_6_2_1_451 95 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 167 282 (accept_3_4 94 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 167 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 167 282 (Polychromatic418967fa.accept_7_1_6_2_1_18 92 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 167 282 (accept_3_4 91 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 167 282 (Polychromatic418967fa.accept_17_5_14_10_1_2831 90 167 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 167 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 167 282 (accept_3_4 88 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 167 282 (Polychromatic418967fa.accept_7_3_6_2_1_90 87 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 167 282 (Polychromatic418967fa.accept_11_9_2_7_1_1298 86 167 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 167 282 (accept_3_4 85 167 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 167 282 (Polychromatic418967fa.accept_10_4_7_2_1_211 84 167
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 167 282
  (Polychromatic418967fa.accept_9_2_5_3_1_37 83 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 167 282 (accept_3_4 82 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 167 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 167 282 (Polychromatic418967fa.accept_7_3_6_2_1_90 80 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 167 282 (accept_3_4 79 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 167 282 (Polychromatic418967fa.accept_7_1_6_2_1_18 78 167 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 167 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 167 282 (accept_3_4 76 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 167 282 (Polychromatic418967fa.accept_10_5_7_2_1_516 75 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 167 282 (Polychromatic418967fa.accept_7_4_6_2_1_451 74 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 167 282 (accept_3_4 73 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 167 282 (Polychromatic418967fa.accept_13_7_11_9_1_1858 72 167 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 167 282
  (Polychromatic418967fa.accept_7_1_6_2_1_18 71 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 167 282 (accept_3_4 70 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 167 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 167 282 (Polychromatic418967fa.accept_19_11_15_16_1_9396 68 167 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 167 282 (accept_3_4 67 167 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 167 282 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 167 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 167 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 167 282 (accept_3_4 64 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 167 282 (Polychromatic418967fa.accept_15_3_2_12_1_2469 63 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 167 282 (Polychromatic418967fa.accept_9_8_5_3_1_777 62 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 167 282 (accept_3_4 61 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 167 282 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 167 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 167 282
  (Polychromatic418967fa.accept_7_3_6_2_1_90 59 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 167 282 (accept_3_4 58 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 167 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 167 282 (Polychromatic418967fa.accept_9_2_5_3_1_37 56 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 167 282 (accept_3_4 55 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 167 282 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 167 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 167 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 167 282 (accept_3_4 52 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 167 282 (Polychromatic418967fa.accept_9_6_5_3_1_205 51 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 167 282 (Polychromatic418967fa.accept_7_1_6_2_1_18 50 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 167 282 (accept_3_4 49 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 167 282 (Polychromatic418967fa.accept_15_3_2_12_1_2469 48 167 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 167 282
  (Polychromatic418967fa.accept_9_2_5_3_1_37 47 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 167 282 (accept_3_4 46 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 167 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 167 282 (Polychromatic418967fa.accept_9_8_5_3_1_777 44 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 167 282 (accept_3_4 43 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 167 282 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 167 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 167 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 167 282 (accept_3_4 40 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 167 282 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 167 282 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 167 282 (accept_3_4 37 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 167 282 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 167 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 167 282
  (Polychromatic418967fa.accept_9_8_5_3_1_777 35 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 167 282 (accept_3_4 34 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 167 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 167 282 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 167 282 (accept_3_4 31 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 167 282 (Polychromatic418967fa.accept_16_14_7_10_1_898 30 167 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 167 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 167 282 (accept_3_4 28 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 167 282 (Polychromatic418967fa.accept_13_1_11_9_1_1857 27 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 167 282 (Polychromatic418967fa.accept_9_8_5_3_1_777 26 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 167 282 (accept_3_4 25 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 167 282 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 167 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 167 282
  (Polychromatic418967fa.accept_21_2_20_9_1_2507 23 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 167 282 (accept_3_4 22 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 167 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 167 282 (Polychromatic418967fa.accept_9_2_5_3_1_37 20 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 167 282 (accept_3_4 19 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 167 282 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 167 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 167 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 167 282 (accept_3_4 16 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 167 282 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 167 282 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 167 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 167 282 (accept_3_4 13 167 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 167 282 (Polychromatic418967fa.accept_19_12_15_16_1_6516 12
  167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 167 282
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 167 282 (accept_3_4 10 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  167 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 167 282 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 167 282 (accept_3_4 7 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 167 282 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 167 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 167 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 167 282 (accept_3_4 4 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  167 282 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 167 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 167 282 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 167 282 (accept_3_4 1 167 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 167
  282))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 117 166 282 (Eq.refl Bool.true) (allA_succ_of_gcd 116 166 282 2 58 83 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 166 282
  (Polychromatic418967fa.accept_7_3_5_2_1_17 115 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 166 282 2 57 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 166 282 (accept_3_5 113 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 166 282 2 56 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 166 282 (Polychromatic418967fa.accept_10_1_6_2_1_867 111 166 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 166 282 2 55 83 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 166 282
  (Polychromatic418967fa.accept_7_4_5_2_1_243 109 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 166 282 2 54 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 166 282 (accept_3_5 107 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 166 282 2 53 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 166 282 (Polychromatic418967fa.accept_9_6_4_3_1_203 105 166 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 166 282 2 52 83 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 166 282
  (Polychromatic418967fa.accept_13_12_10_9_1_1166 103 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 166 282 2 51 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 166 282 (accept_3_5 101 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 166 282 2 50 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 166 282 (Polychromatic418967fa.accept_12_3_10_6_1_442 99 166 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 166 282 2 49 83 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 166 282
  (Polychromatic418967fa.accept_9_7_4_3_1_204 97 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 166 282 2 48 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 166 282 (accept_3_5 95 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 166 282 2 47 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 166 282 (Polychromatic418967fa.accept_12_9_10_6_1_872 93 166 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 166 282 2 46 83 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 166 282
  (Polychromatic418967fa.accept_9_1_4_3_1_201 91 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 166 282 2 45 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 166 282 (accept_3_5 89 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 166 282 2 44 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 166 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 87 166 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 166 282 2 43 83 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 166 282
  (Polychromatic418967fa.accept_19_9_14_16_1_3791 85 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 166 282 2 42 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 166 282 (accept_3_5 83 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 166 282 2 41 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 166 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 81 166 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 166 282 2 40 83 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 166 282
  (Polychromatic418967fa.accept_9_7_4_3_1_204 79 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 166 282 2 39 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 166 282 (accept_3_5 77 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 166 282 2 38 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 166 282 (Polychromatic418967fa.accept_12_3_10_6_1_442 75 166 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 166 282 2 37 83 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 166 282
  (Polychromatic418967fa.accept_7_3_5_2_1_17 73 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 166 282 2 36 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 166 282 (accept_3_5 71 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 166 282 2 35 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 166 282 (Polychromatic418967fa.accept_9_6_4_3_1_203 69 166 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 166 282 2 34 83 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 166 282
  (Polychromatic418967fa.accept_7_4_5_2_1_243 67 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 166 282 2 33 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 166 282 (accept_3_5 65 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 166 282 2 32 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 166 282 (Polychromatic418967fa.accept_12_3_10_6_1_442 63 166 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 166 282 2 31 83 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 166 282
  (Polychromatic418967fa.accept_9_7_4_3_1_204 61 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 166 282 2 30 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 166 282 (accept_3_5 59 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 166 282 2 29 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 166 282 (Polychromatic418967fa.accept_12_9_10_6_1_872 57 166 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 166 282 2 28 83 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 166 282
  (Polychromatic418967fa.accept_9_1_4_3_1_201 55 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 166 282 2 27 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 166 282 (accept_3_5 53 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 166 282 2 26 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 166 282 (Polychromatic418967fa.accept_9_6_4_3_1_203 51 166 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 166 282 2 25 83 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 166 282
  (Polychromatic418967fa.accept_14_7_12_2_1_2502 49 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 166 282 2 24 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 166 282 (accept_3_5 47 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 166 282 2 23 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 166 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 166 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 166 282 2 22 83 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 166 282
  (Polychromatic418967fa.accept_9_7_4_3_1_204 43 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 166 282 2 21 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 166 282 (accept_3_5 41 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 166 282 2 20 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 166 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 166 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 166 282 2 19 83 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 166 282
  (Polychromatic418967fa.accept_9_1_4_3_1_201 37 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 166 282 2 18 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 166 282 (accept_3_5 35 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 166 282 2 17 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 166 282 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 166 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 166 282 2 16 83 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 166 282
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 166 282 2 15 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 166 282 (accept_3_5 29 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 166 282 2 14 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 166 282 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 166 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 166 282 2 13 83 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 166 282
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 166 282 2 12 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 166 282 (accept_3_5 23 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 166 282 2 11 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 166 282 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 166 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 166 282 2 10 83 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 166 282
  (Polychromatic418967fa.accept_9_1_4_3_1_201 19 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 166 282 2 9 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 166 282 (accept_3_5 17 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 166 282 2 8 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 166 282 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 166 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 166 282 2 7 83 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 166 282
  (Polychromatic418967fa.accept_15_13_1_12_1_1638 13 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 166 282 2 6 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 166 282 (accept_3_5 11 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 166 282 2 5 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 166 282 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 166 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 166 282 2 4 83 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 166 282
  (Polychromatic418967fa.accept_9_7_4_3_1_204 7 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 166 282 2 3 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 166 282 (accept_3_5 5 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 166
  282 2 2 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  166 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 166 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 166 282 2 1 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 166 282 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 166 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166
  282)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 118 165 282 (Eq.refl Bool.true) (allA_succ_of_gcd 117 165 282 3 39 55 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 116 165 282
  (Polychromatic418967fa.accept_12_8_9_6_1_127 116 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 165 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 115 165 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 165 282 3 38 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 165 282 (Polychromatic418967fa.accept_10_3_5_2_1_38
  113 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 165 282
  (Polychromatic418967fa.accept_12_4_9_6_1_440 112 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 111 165 282 3 37 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 110 165 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 110 165 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 165 282
  (Polychromatic418967fa.accept_16_13_5_10_1_1680 109 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 108 165 282 3 36 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 107 165 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 107 165 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 165 282
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 106 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 105 165 282 3 35 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 104 165 282 (Polychromatic418967fa.accept_7_6_4_2_1_236 104 165 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 165 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 103 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 165 282 3 34 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 165 282 (Polychromatic418967fa.accept_21_17_18_9_1_9968 101 165 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 165 282
  (Polychromatic418967fa.accept_12_4_9_6_1_440 100 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 165 282 3 33 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 165 282 (Polychromatic418967fa.accept_10_8_5_2_1_881 98 165 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 165 282 (Polychromatic418967fa.accept_7_6_4_2_1_236
  97 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 165 282 3 32 55 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 165 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 95 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 165 282 (Polychromatic418967fa.accept_12_10_9_6_1_1445 94 165 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 165 282 3 31 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 165 282 (Polychromatic418967fa.accept_12_8_9_6_1_127
  92 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 165 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 91 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 165 282 3 30 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 165 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 89 165 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 165 282 (Polychromatic418967fa.accept_10_8_5_2_1_881
  88 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 165 282 3 29 55 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 165 282
  (Polychromatic418967fa.accept_12_2_9_6_1_439 86 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 165 282 (Polychromatic418967fa.accept_18_13_3_12_1_3207 85 165 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 165 282 3 28 55 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 165 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 165 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 82 165 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 165 282 3 27 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 165 282 (Polychromatic418967fa.accept_12_8_9_6_1_127
  80 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 165 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 79 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 165 282 3 26 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 165 282 (Polychromatic418967fa.accept_10_7_5_2_1_880 77 165 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 165 282 (Polychromatic418967fa.accept_7_6_4_2_1_236
  76 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 165 282 3 25 55 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 165 282
  (Polychromatic418967fa.accept_12_2_9_6_1_439 74 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 165 282 (Polychromatic418967fa.accept_10_3_5_2_1_38 73 165 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 165 282 3 24 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 165 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 71
  165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 165 282
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 70 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 165 282 3 23 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 165 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 68 165 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 165 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 67
  165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 165 282 3 22 55 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 165 282
  (Polychromatic418967fa.accept_14_9_11_2_1_2501 65 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 165 282 (Polychromatic418967fa.accept_12_4_9_6_1_440 64 165 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 165 282 3 21 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 165 282 (Polychromatic418967fa.accept_7_6_4_2_1_236 62
  165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 165 282
  (Polychromatic418967fa.accept_7_5_4_2_1_235 61 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 165 282 3 20 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 165 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 165 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 165 282 (Polychromatic418967fa.accept_10_8_5_2_1_881
  58 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 165 282 3 19 55 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 165 282
  (Polychromatic418967fa.accept_12_8_9_6_1_127 56 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 165 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 165 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 165 282 3 18 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 165 282 (Polychromatic418967fa.accept_10_3_5_2_1_38 53
  165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 165 282
  (Polychromatic418967fa.accept_12_4_9_6_1_440 52 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 165 282 3 17 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 165 282 (Polychromatic418967fa.accept_12_2_9_6_1_439 50 165 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 165 282
  (Polychromatic418967fa.accept_18_13_3_12_1_3207 49 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 165 282 3 16 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 165 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 165 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 165 282
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 46 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 165 282 3 15 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 165 282 (Polychromatic418967fa.accept_12_8_9_6_1_127 44 165 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 165 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 43
  165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 165 282 3 14 55 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 165 282
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 165 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 165 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 165 282 3 13 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 165 282 (Polychromatic418967fa.accept_10_8_5_2_1_881
  38 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 165 282
  (Polychromatic418967fa.accept_10_7_5_2_1_880 37 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 165 282 3 12 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 165 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 165 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 165 282 (Polychromatic418967fa.accept_7_6_4_2_1_236
  34 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 165 282 3 11 55 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 165 282
  (Polychromatic418967fa.accept_12_8_9_6_1_127 32 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 165 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 165 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 165 282 3 10 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 165 282
  (Polychromatic418967fa.accept_16_13_5_10_1_1680 29 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 165 282 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 165 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 165 282 3 9 55 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 165 282
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 165 282 (Polychromatic418967fa.accept_17_8_12_10_1_6442 25 165 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 165 282 3 8 55 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 165 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 165 282 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 165 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 165 282 3 7 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 165 282 (Polychromatic418967fa.accept_7_6_4_2_1_236 20
  165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 165 282 3 6 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 165 282 (Polychromatic418967fa.accept_10_7_5_2_1_880 17 165 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 282 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 165
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 165 282 3 5 55 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 165 282
  (Polychromatic418967fa.accept_12_2_9_6_1_439 14 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 165 282 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 165 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 165 282 3 4 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 165 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 165 282
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 165 282 3 3 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 165 282 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 165 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 165 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 165 282 3 2 55 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 165 282
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 165 282 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 165 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 165 282 3 1 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 165 282 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 165 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 282
  (Polychromatic418967fa.accept_18_1_3_12_1_467 1 165 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 165
  282))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 119 164 282 (Eq.refl Bool.true) (allA_succ_of_gcd 118 164 282 2 59 82 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 164 282
  (Polychromatic418967fa.accept_7_5_3_2_1_249 117 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 164 282 2 58 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 164 282 (accept_3_4 115 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 164 282 2 57 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 164 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 113 164 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 164 282 2 56 82 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 164 282
  (Polychromatic418967fa.accept_7_6_3_2_1_461 111 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 164 282 2 55 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 164 282 (accept_3_4 109 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 164 282 2 54 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 164 282 (Polychromatic418967fa.accept_9_8_2_3_1_447 107 164 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 164 282 2 53 82 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 164 282
  (Polychromatic418967fa.accept_9_6_2_3_1_771 105 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 164 282 2 52 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 164 282 (accept_3_4 103 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 164 282 2 51 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 164 282 (Polychromatic418967fa.accept_15_11_14_12_1_2458 101 164 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 164 282 2 50 82 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 164 282
  (Polychromatic418967fa.accept_7_1_3_2_1_13 99 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 164 282 2 49 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 164 282 (accept_3_4 97 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 164 282 2 48 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 164 282 (Polychromatic418967fa.accept_9_5_2_3_1_194 95 164 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 164 282 2 47 82 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 164 282
  (Polychromatic418967fa.accept_12_9_8_6_1_466 93 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 164 282 2 46 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 164 282 (accept_3_4 91 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 164 282 2 45 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 164 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 89 164 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 164 282 2 44 82 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 164 282
  (Polychromatic418967fa.accept_9_6_2_3_1_771 87 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 164 282 2 43 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 164 282 (accept_3_4 85 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 164 282 2 42 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 164 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 83 164 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 164 282 2 41 82 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 164 282
  (Polychromatic418967fa.accept_12_9_8_6_1_466 81 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 164 282 2 40 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 164 282 (accept_3_4 79 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 164 282 2 39 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 164 282 (Polychromatic418967fa.accept_9_5_2_3_1_194 77 164 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 164 282 2 38 82 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 164 282
  (Polychromatic418967fa.accept_7_5_3_2_1_249 75 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 164 282 2 37 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 164 282 (accept_3_4 73 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 164 282 2 36 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 164 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 71 164 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 164 282 2 35 82 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 164 282
  (Polychromatic418967fa.accept_7_6_3_2_1_461 69 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 164 282 2 34 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 164 282 (accept_3_4 67 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 164 282 2 33 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 164 282 (Polychromatic418967fa.accept_20_5_4_2_1_5912 65 164 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 164 282 2 32 82 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 164 282
  (Polychromatic418967fa.accept_12_3_8_6_1_895 63 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 164 282 2 31 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 164 282 (accept_3_4 61 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 164 282 2 30 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 164 282 (Polychromatic418967fa.accept_9_5_2_3_1_194 59 164 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 164 282 2 29 82 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 164 282
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 164 282 2 28 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 164 282 (accept_3_4 55 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 164 282 2 27 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 164 282 (Polychromatic418967fa.accept_9_8_2_3_1_447 53 164 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 164 282 2 26 82 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 164 282
  (Polychromatic418967fa.accept_9_6_2_3_1_771 51 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 164 282 2 25 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 164 282 (accept_3_4 49 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 164 282 2 24 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 164 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 164 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 164 282 2 23 82 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 164 282
  (Polychromatic418967fa.accept_12_9_8_6_1_466 45 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 164 282 2 22 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 164 282 (accept_3_4 43 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 164 282 2 21 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 164 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 164 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 164 282 2 20 82 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 164 282
  (Polychromatic418967fa.accept_12_3_8_6_1_895 39 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 164 282 2 19 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 164 282 (accept_3_4 37 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 164 282 2 18 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 164 282 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 164 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 164 282 2 17 82 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 164 282
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 164 282 2 16 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 164 282 (accept_3_4 31 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 164 282 2 15 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 164 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 164 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 164 282 2 14 82 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 164 282
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 164 282 2 13 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 164 282 (accept_3_4 25 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 164 282 2 12 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 164 282 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 164 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 164 282 2 11 82 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 164 282
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 164 282 2 10 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 164 282 (accept_3_4 19 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 164 282 2 9 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 164 282 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 164 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 164 282 2 8 82 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 164 282
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 164 282 2 7 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 164 282 (accept_3_4 13 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 164 282 2 6 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 164 282 (Polychromatic418967fa.accept_13_11_8_9_1_1161 11 164 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 164 282 2 5 82 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 164 282
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 164 282 2 4 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 164 282 (accept_3_4 7 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 164
  282 2 3 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  164 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 164 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 164 282 2 2 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 164 282 (Polychromatic418967fa.accept_11_3_10_7_1_129 3 164 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 164 282 2 1 82 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 164 282 (accept_3_4 1 164 282
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164
  282)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 120 163 282 (Eq.refl Bool.true) (allA_succ_of_accept 119 163 282 (accept_3_5 119 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 163 282 (Polychromatic418967fa.accept_19_4_11_16_1_1474 118
  163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 163 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 117 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 163 282 (accept_3_5 116 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 163 282 (Polychromatic418967fa.accept_9_7_1_3_1_443 115 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 163 282 (Polychromatic418967fa.accept_9_6_1_3_1_191 114 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 163 282 (accept_3_5 113 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 163 282 (Polychromatic418967fa.accept_9_4_1_3_1_190 112 163
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 163 282
  (Polychromatic418967fa.accept_10_1_3_2_1_220 111 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 163 282 (accept_3_5 110 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 163 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 109 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 163 282 (Polychromatic418967fa.accept_13_4_7_9_1_5260 108 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 163 282 (accept_3_5 107 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 163 282 (Polychromatic418967fa.accept_9_7_1_3_1_443 106 163
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 163 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 105 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 163 282 (accept_3_5 104 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 163 282 (Polychromatic418967fa.accept_9_4_1_3_1_190 103 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 163 282 (Polychromatic418967fa.accept_13_11_7_9_1_612 102 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 163 282 (accept_3_5 101 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 163 282 (Polychromatic418967fa.accept_15_10_13_12_1_3384 100
  163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 163 282
  (Polychromatic418967fa.accept_13_8_7_9_1_611 99 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 163 282 (accept_3_5 98 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 163 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 163 282 (Polychromatic418967fa.accept_9_6_1_3_1_191 96 163 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 163 282 (accept_3_5 95 163 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 163 282 (Polychromatic418967fa.accept_9_4_1_3_1_190 94 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 163 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 93 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 163 282 (accept_3_5 92 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 163 282 (Polychromatic418967fa.accept_10_1_3_2_1_220 91 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 163 282 (Polychromatic418967fa.accept_11_2_9_7_1_124 90 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 163 282 (accept_3_5 89 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 163 282 (Polychromatic418967fa.accept_9_7_1_3_1_443 88 163 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 163 282
  (Polychromatic418967fa.accept_9_6_1_3_1_191 87 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 163 282 (accept_3_5 86 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 163 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 163 282 (Polychromatic418967fa.accept_13_6_7_9_1_1848 84 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 163 282 (accept_3_5 83 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 163 282 (Polychromatic418967fa.accept_11_5_9_7_1_411 82 163
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 163 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 163 282 (accept_3_5 80 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 163 282 (Polychromatic418967fa.accept_9_7_1_3_1_443 79 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 163 282 (Polychromatic418967fa.accept_9_6_1_3_1_191 78 163 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 163 282 (accept_3_5 77 163 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 163 282 (Polychromatic418967fa.accept_9_4_1_3_1_190 76 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 163 282
  (Polychromatic418967fa.accept_10_5_3_2_1_899 75 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 163 282 (accept_3_5 74 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 163 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 163 282 (Polychromatic418967fa.accept_19_15_11_16_1_6492 72 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 163 282 (accept_3_5 71 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 163 282 (Polychromatic418967fa.accept_9_7_1_3_1_443 70 163 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 163 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 163 282 (accept_3_5 68 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 163 282 (Polychromatic418967fa.accept_9_4_1_3_1_190 67 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 163 282 (Polychromatic418967fa.accept_21_3_16_9_1_8528 66 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 163 282 (accept_3_5 65 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 163 282 (Polychromatic418967fa.accept_22_20_9_18_1_8087 64 163
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 163 282
  (Polychromatic418967fa.accept_13_11_7_9_1_612 63 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 163 282 (accept_3_5 62 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 163 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 163 282 (Polychromatic418967fa.accept_9_6_1_3_1_191 60 163 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 163 282 (accept_3_5 59 163 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 163 282 (Polychromatic418967fa.accept_9_4_1_3_1_190 58 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 163 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 163 282 (accept_3_5 56 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 163 282 (Polychromatic418967fa.accept_10_5_3_2_1_899 55 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 163 282 (Polychromatic418967fa.accept_13_2_7_9_1_2616 54 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 163 282 (accept_3_5 53 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 163 282 (Polychromatic418967fa.accept_9_7_1_3_1_443 52 163 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 163 282
  (Polychromatic418967fa.accept_9_6_1_3_1_191 51 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 163 282 (accept_3_5 50 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 163 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 163 282 (Polychromatic418967fa.accept_15_3_13_12_1_348 48 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 163 282 (accept_3_5 47 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 163 282 (Polychromatic418967fa.accept_11_2_9_7_1_124 46 163
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 163 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 163 282 (accept_3_5 44 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 163 282 (Polychromatic418967fa.accept_9_7_1_3_1_443 43 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 163 282 (Polychromatic418967fa.accept_9_6_1_3_1_191 42 163 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 163 282 (accept_3_5 41 163 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 163 282 (Polychromatic418967fa.accept_9_4_1_3_1_190 40 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 163 282
  (Polychromatic418967fa.accept_14_11_9_2_1_6382 39 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 163 282 (accept_3_5 38 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 163 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 163 282 (Polychromatic418967fa.accept_21_15_16_9_1_5303 36 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 163 282 (accept_3_5 35 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 163 282 (Polychromatic418967fa.accept_9_7_1_3_1_443 34 163 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 163 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 163 282 (accept_3_5 32 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 163 282 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 163 282 (Polychromatic418967fa.accept_13_4_7_9_1_5260 30 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 163 282 (accept_3_5 29 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 163 282 (Polychromatic418967fa.accept_13_2_7_9_1_2616 28 163
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 163 282
  (Polychromatic418967fa.accept_11_5_9_7_1_411 27 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 163 282 (accept_3_5 26 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 163 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 163 282 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 163 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 163 282 (accept_3_5 23 163 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 163 282 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 163 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 163 282 (accept_3_5 20 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 163 282 (Polychromatic418967fa.accept_13_6_7_9_1_1848 19 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 163 282 (Polychromatic418967fa.accept_14_4_9_2_1_95 18 163 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 163 282 (accept_3_5 17 163 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 163 282 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 163 282
  (Polychromatic418967fa.accept_9_6_1_3_1_191 15 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 163 282 (accept_3_5 14 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 163 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 163 282 (Polychromatic418967fa.accept_16_12_3_10_1_3524 12 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 163 282 (accept_3_5 11 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 163 282 (Polychromatic418967fa.accept_15_10_13_12_1_3384 10
  163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 163 282 (accept_3_5 8 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  163 282 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 163 282 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 163 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 163 282 (accept_3_5 5 163 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 163 282 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 163 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 163 282
  (Polychromatic418967fa.accept_13_3_7_9_1_1153 3 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 163 282 (accept_3_5 2 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  163 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 163 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 163
  282))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 121 162 282 (Eq.refl Bool.true) (allA_succ_of_gcd 120 162 282 6 20 27 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 162 282
  (Polychromatic418967fa.accept_13_2_6_9_1_2636 119 162 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 162 282 2 59 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 117 162 282 3 39 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 116 162 282 2 58 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 162 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 115 162
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 162 282 6 19 27 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 162 282
  (Polychromatic418967fa.accept_14_1_8_2_1_1675 113 162 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 162 282 2 56 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 111 162 282 3 37 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 110 162 282 2 55 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 162 282 (Polychromatic418967fa.accept_21_4_15_9_1_3839 109 162
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 162 282 6 18 27 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 162 282
  (Polychromatic418967fa.accept_13_3_6_9_1_1150 107 162 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 162 282 2 53 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 105 162 282 3 35 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 104 162 282 2 52 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 162 282 (Polychromatic418967fa.accept_11_4_8_7_1_819 103 162
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 162 282 6 17 27 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 162 282
  (Polychromatic418967fa.accept_7_3_1_2_1_247 101 162 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 162 282 2 50 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 99 162 282 3 33 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 98 162 282 2 49 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 162 282 (Polychromatic418967fa.accept_7_6_1_2_1_230 97 162 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 162 282 6 16 27 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 162 282
  (Polychromatic418967fa.accept_13_4_6_9_1_3401 95 162 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 162 282 2 47 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 93 162 282 3 31 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 92 162 282 2 46 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 162 282 (Polychromatic418967fa.accept_21_7_15_9_1_5289 91 162
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 162 282 6 15 27 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 162 282
  (Polychromatic418967fa.accept_19_13_10_16_1_9334 89 162 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 162 282 2 44 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 87 162 282 3 29 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 162 282 2 43 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 162 282 (Polychromatic418967fa.accept_13_7_6_9_1_1831
  85 162 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 162 282 6 14 27 47
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 162 282
  (Polychromatic418967fa.accept_7_6_1_2_1_230 83 162 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 162 282 2 41 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 162 282 3 27 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 80 162 282 2 40 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 162 282 (Polychromatic418967fa.accept_13_1_6_9_1_1197 79 162
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 162 282 6 13 27 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 162 282
  (Polychromatic418967fa.accept_19_1_10_16_1_6510 77 162 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 162 282 2 38 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 75 162 282 3 25 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 162 282 2 37 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 162 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 73
  162 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 162 282 6 12 27 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 162 282
  (Polychromatic418967fa.accept_14_1_8_2_1_1675 71 162 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 162 282 2 35 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 162 282 3 23 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 162 282 2 34 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 162 282 (Polychromatic418967fa.accept_13_2_6_9_1_2636 67 162
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 162 282 6 11 27 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 162 282
  (Polychromatic418967fa.accept_19_8_10_16_1_9418 65 162 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 162 282 2 32 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 63 162 282 3 21 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 162 282 2 31 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 162 282
  (Polychromatic418967fa.accept_19_4_10_16_1_6531 61 162 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 162 282 6 10 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 162 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 162 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 162 282 2 29 81 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 162 282 3 19 54 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 162 282 2 28 81 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 162 282
  (Polychromatic418967fa.accept_7_6_1_2_1_230 55 162 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 162 282 6 9 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 162 282 (Polychromatic418967fa.accept_13_1_6_9_1_1197 53 162 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 162 282 2 26 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 162 282 3 17 54 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 162 282 2 25 81 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 162 282
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 49 162 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 162 282 6 8 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 162 282 (Polychromatic418967fa.accept_17_13_9_10_1_2888 47 162 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 162 282 2 23 81 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 162 282 3 15 54 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 162 282 2 22 81 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 162 282
  (Polychromatic418967fa.accept_13_4_6_9_1_3401 43 162 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 162 282 6 7 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 162 282 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 162 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 162 282 2 20 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 162 282 3 13 54 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 162 282 2 19 81 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 162 282
  (Polychromatic418967fa.accept_11_4_8_7_1_819 37 162 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 162 282 6 6 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 162 282 (Polychromatic418967fa.accept_17_1_9_10_1_1864 35 162 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 162 282 2 17 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 162 282 3 11 54 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 162 282 2 16 81 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 162 282
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 162 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 282 6 5 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 162 282 (Polychromatic418967fa.accept_13_3_6_9_1_1150 29 162 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 162 282 2 14 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 162 282 3 9 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 162 282 2 13 81 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 162 282
  (Polychromatic418967fa.accept_19_6_10_16_1_7989 25 162 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 162 282 6 4 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 162 282 (Polychromatic418967fa.accept_13_10_6_9_1_1152 23 162 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 162 282 2 11 81 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 162 282 3 7 54 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 162 282 2 10 81 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 162 282
  (Polychromatic418967fa.accept_21_19_15_9_1_11533 19 162 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 162 282 6 3 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 162 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 162 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 162 282 2 8 81 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 162 282 3 5 54 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 162 282 2 7 81 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 162 282
  (Polychromatic418967fa.accept_7_6_1_2_1_230 13 162 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 162 282 6 2 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 162 282 (Polychromatic418967fa.accept_21_11_15_9_1_3868 11 162 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 162 282 2 5 81 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 162 282 3 3 54 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 162 282 2 4 81 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 162 282
  (Polychromatic418967fa.accept_13_7_6_9_1_1831 7 162 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 162 282 6 1 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 162 282 (Polychromatic418967fa.accept_19_5_10_16_1_6507 5 162 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 162 282 2 2 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 162 282 3 1 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 162 282 2 1 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 282 (Polychromatic418967fa.accept_13_1_6_9_1_1197 1
  162 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  282)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 122 161 282 (Eq.refl Bool.true) (allA_succ_of_accept 121 161 282 (accept_3_4 121 161 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 161 282 (Polychromatic418967fa.accept_13_3_5_9_1_5285 120 161
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 161 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 119 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 161 282 (accept_3_4 118 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 161 282 (Polychromatic418967fa.accept_14_5_7_2_1_468 117 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 161 282 (Polychromatic418967fa.accept_10_6_1_2_1_874 116 161 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 161 282 (accept_3_4 115 161 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 161 282 (Polychromatic418967fa.accept_9_6_8_3_1_183 114 161
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 161 282
  (Polychromatic418967fa.accept_9_5_8_3_1_437 113 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 161 282 (accept_3_4 112 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 161 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 111 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 161 282 (Polychromatic418967fa.accept_9_2_8_3_1_181 110 161 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 161 282 (accept_3_4 109 161 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 161 282 (Polychromatic418967fa.accept_13_4_5_9_1_1829 108 161
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 161 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 107 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 161 282 (accept_3_4 106 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 161 282 (Polychromatic418967fa.accept_9_6_8_3_1_183 105 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 161 282 (Polychromatic418967fa.accept_9_5_8_3_1_437 104 161 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 161 282 (accept_3_4 103 161 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 161 282 (Polychromatic418967fa.accept_19_7_9_16_1_10774 102
  161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 161 282
  (Polychromatic418967fa.accept_9_2_8_3_1_181 101 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 161 282 (accept_3_4 100 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 161 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 161 282 (Polychromatic418967fa.accept_15_8_11_12_1_1626 98 161 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 161 282 (accept_3_4 97 161 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 161 282 (Polychromatic418967fa.accept_9_6_8_3_1_183 96 161 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 161 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 95 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 161 282 (accept_3_4 94 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 161 282 (Polychromatic418967fa.accept_10_3_1_2_1_521 93 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 161 282 (Polychromatic418967fa.accept_9_2_8_3_1_181 92 161 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 161 282 (accept_3_4 91 161 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 161 282 (Polychromatic418967fa.accept_19_14_9_16_1_7969 90 161 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 161 282
  (Polychromatic418967fa.accept_10_9_1_2_1_522 89 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 161 282 (accept_3_4 88 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 161 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 161 282 (Polychromatic418967fa.accept_9_5_8_3_1_437 86 161 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 161 282 (accept_3_4 85 161 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 161 282 (Polychromatic418967fa.accept_19_8_9_16_1_9406 84 161 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 161 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 161 282 (accept_3_4 82 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 161 282 (Polychromatic418967fa.accept_13_3_5_9_1_5285 81 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 161 282 (Polychromatic418967fa.accept_13_2_5_9_1_610 80 161 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 161 282 (accept_3_4 79 161 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 161 282 (Polychromatic418967fa.accept_9_6_8_3_1_183 78 161 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 161 282
  (Polychromatic418967fa.accept_9_5_8_3_1_437 77 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 161 282 (accept_3_4 76 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 161 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 161 282 (Polychromatic418967fa.accept_9_2_8_3_1_181 74 161 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 161 282 (accept_3_4 73 161 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 161 282 (Polychromatic418967fa.accept_22_6_7_18_1_9725 72 161 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 161 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 161 282 (accept_3_4 70 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 161 282 (Polychromatic418967fa.accept_9_6_8_3_1_183 69 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 161 282 (Polychromatic418967fa.accept_9_5_8_3_1_437 68 161 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 161 282 (accept_3_4 67 161 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 161 282 (Polychromatic418967fa.accept_10_6_1_2_1_874 66 161 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 161 282
  (Polychromatic418967fa.accept_9_2_8_3_1_181 65 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 161 282 (accept_3_4 64 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 161 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 161 282 (Polychromatic418967fa.accept_21_20_14_9_1_11573 62 161 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 161 282 (accept_3_4 61 161 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 161 282 (Polychromatic418967fa.accept_9_6_8_3_1_183 60 161 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 161 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 161 282 (accept_3_4 58 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 161 282 (Polychromatic418967fa.accept_16_9_1_10_1_3610 57 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 161 282 (Polychromatic418967fa.accept_9_2_8_3_1_181 56 161 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 161 282 (accept_3_4 55 161 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 161 282 (Polychromatic418967fa.accept_13_2_5_9_1_610 54 161 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 161 282
  (Polychromatic418967fa.accept_10_3_1_2_1_521 53 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 161 282 (accept_3_4 52 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 161 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 161 282 (Polychromatic418967fa.accept_9_5_8_3_1_437 50 161 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 161 282 (accept_3_4 49 161 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 161 282 (Polychromatic418967fa.accept_19_10_9_16_1_5085 48 161 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 161 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 161 282 (accept_3_4 46 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 161 282 (Polychromatic418967fa.accept_18_9_17_12_1_462 45 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 161 282 (Polychromatic418967fa.accept_15_14_11_12_1_4440 44 161 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 161 282 (accept_3_4 43 161 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 161 282 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 161 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 161 282
  (Polychromatic418967fa.accept_9_5_8_3_1_437 41 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 161 282 (accept_3_4 40 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 161 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 161 282 (Polychromatic418967fa.accept_9_2_8_3_1_181 38 161 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 161 282 (accept_3_4 37 161 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 161 282 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 161 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 161 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 161 282 (accept_3_4 34 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 161 282 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 161 282 (Polychromatic418967fa.accept_9_5_8_3_1_437 32 161 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 161 282 (accept_3_4 31 161 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 161 282 (Polychromatic418967fa.accept_13_4_5_9_1_1829 30 161 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 161 282
  (Polychromatic418967fa.accept_9_2_8_3_1_181 29 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 161 282 (accept_3_4 28 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 161 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 161 282 (Polychromatic418967fa.accept_10_6_1_2_1_874 26 161 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 161 282 (accept_3_4 25 161 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 161 282 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 161 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 161 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 161 282 (accept_3_4 22 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 161 282 (Polychromatic418967fa.accept_25_21_11_7_1_17312 21 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 20 161 282 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 161 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 161 282 (accept_3_4 19 161 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 161 282 (Polychromatic418967fa.accept_19_18_9_16_1_6524 18 161
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 161 282
  (Polychromatic418967fa.accept_13_4_5_9_1_1829 17 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 161 282 (accept_3_4 16 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 161 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 161 282 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 161 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 161 282 (accept_3_4 13 161 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 161 282 (Polychromatic418967fa.accept_14_12_7_2_1_1663 12 161 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 161 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 161 282 (accept_3_4 10 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  161 282 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 161 282 (Polychromatic418967fa.accept_15_8_11_12_1_1626 8 161 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 161 282 (accept_3_4 7 161 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 161 282 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 161 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 282
  (Polychromatic418967fa.accept_9_5_8_3_1_437 5 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 161 282 (accept_3_4 4 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  161 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 161 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 161 282 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 161 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 161 282 (accept_3_4 1 161 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 161
  282))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 123 160 282 (Eq.refl Bool.true) (allA_succ_of_gcd 122 160 282 2 61 80 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 160 282
  (Polychromatic418967fa.accept_9_4_7_3_1_43 121 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 160 282 2 60 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 160 282 (accept_3_5 119 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 160 282 2 59 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 160 282 (Polychromatic418967fa.accept_12_9_4_6_1_460 117 160 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 160 282 2 58 80 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 160 282
  (Polychromatic418967fa.accept_7_3_6_2_1_90 115 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 160 282 2 57 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 160 282 (accept_3_5 113 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 160 282 2 56 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 160 282 (Polychromatic418967fa.accept_11_1_6_7_1_116 111 160 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 160 282 2 55 80 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 160 282
  (Polychromatic418967fa.accept_7_4_6_2_1_451 109 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 160 282 2 54 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 160 282 (accept_3_5 107 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 160 282 2 53 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 160 282 (Polychromatic418967fa.accept_9_6_7_3_1_436 105 160 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 160 282 2 52 80 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 160 282
  (Polychromatic418967fa.accept_9_4_7_3_1_43 103 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 160 282 2 51 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 160 282 (accept_3_5 101 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 160 282 2 50 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 160 282 (Polychromatic418967fa.accept_7_1_6_2_1_18 99 160 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 160 282 2 49 80 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 160 282
  (Polychromatic418967fa.accept_13_6_4_9_1_4326 97 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 160 282 2 48 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 160 282 (accept_3_5 95 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 160 282 2 47 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 160 282 (Polychromatic418967fa.accept_12_9_4_6_1_460 93 160 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 160 282 2 46 80 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 160 282
  (Polychromatic418967fa.accept_9_1_7_3_1_41 91 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 160 282 2 45 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 160 282 (accept_3_5 89 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 160 282 2 44 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 160 282 (Polychromatic418967fa.accept_7_3_6_2_1_90 87 160 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 160 282 2 43 80 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 160 282
  (Polychromatic418967fa.accept_7_1_6_2_1_18 85 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 160 282 2 42 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 160 282 (accept_3_5 83 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 160 282 2 41 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 160 282 (Polychromatic418967fa.accept_7_4_6_2_1_451 81 160 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 160 282 2 40 80 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 160 282
  (Polychromatic418967fa.accept_21_16_13_9_1_2539 79 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 160 282 2 39 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 160 282 (accept_3_5 77 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 160 282 2 38 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 160 282 (Polychromatic418967fa.accept_12_3_4_6_1_434 75 160 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 160 282 2 37 80 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 160 282
  (Polychromatic418967fa.accept_7_3_6_2_1_90 73 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 160 282 2 36 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 160 282 (accept_3_5 71 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 160 282 2 35 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 160 282 (Polychromatic418967fa.accept_9_6_7_3_1_436 69 160 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 160 282 2 34 80 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 160 282
  (Polychromatic418967fa.accept_7_4_6_2_1_451 67 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 160 282 2 33 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 160 282 (accept_3_5 65 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 160 282 2 32 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 160 282 (Polychromatic418967fa.accept_12_3_4_6_1_434 63 160 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 160 282 2 31 80 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 160 282
  (Polychromatic418967fa.accept_50_11_10_32_1_17311 61 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 160 282 2 30 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 160 282 (accept_3_5 59 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 160 282 2 29 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 160 282 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 160 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 160 282 2 28 80 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 160 282
  (Polychromatic418967fa.accept_9_1_7_3_1_41 55 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 160 282 2 27 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 160 282 (accept_3_5 53 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 160 282 2 26 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 160 282 (Polychromatic418967fa.accept_9_6_7_3_1_436 51 160 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 160 282 2 25 80 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 160 282
  (Polychromatic418967fa.accept_9_4_7_3_1_43 49 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 160 282 2 24 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 160 282 (accept_3_5 47 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 160 282 2 23 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 160 282 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 160 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 160 282 2 22 80 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 160 282
  (Polychromatic418967fa.accept_7_1_6_2_1_18 43 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 160 282 2 21 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 160 282 (accept_3_5 41 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 160 282 2 20 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 160 282 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 160 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 160 282 2 19 80 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 160 282
  (Polychromatic418967fa.accept_9_1_7_3_1_41 37 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 160 282 2 18 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 160 282 (accept_3_5 35 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 160 282 2 17 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 160 282 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 160 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 160 282 2 16 80 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 160 282
  (Polychromatic418967fa.accept_7_3_6_2_1_90 31 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 160 282 2 15 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 160 282 (accept_3_5 29 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 160 282 2 14 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 160 282 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 160 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 160 282 2 13 80 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 160 282
  (Polychromatic418967fa.accept_7_4_6_2_1_451 25 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 160 282 2 12 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 160 282 (accept_3_5 23 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 160 282 2 11 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 160 282 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 160 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 160 282 2 10 80 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 160 282
  (Polychromatic418967fa.accept_9_1_7_3_1_41 19 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 160 282 2 9 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 160 282 (accept_3_5 17 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 160 282 2 8 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 160 282 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 160 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 160 282 2 7 80 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 160 282
  (Polychromatic418967fa.accept_9_4_7_3_1_43 13 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 160 282 2 6 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 160 282 (accept_3_5 11 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 160 282 2 5 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 160 282 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 160 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 160 282 2 4 80 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 160 282
  (Polychromatic418967fa.accept_13_7_4_9_1_1865 7 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 160 282 2 3 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 160 282 (accept_3_5 5 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 160
  282 2 2 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  160 282 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 160 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 160 282 2 1 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 160 282 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 160 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160
  282)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 124 159 282 (Eq.refl Bool.true) (allA_succ_of_gcd 123 159 282 3 41 53 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 122 159 282
  (Polychromatic418967fa.accept_7_3_5_2_1_17 122 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 159 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 121 159 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 159 282 3 40 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 159 282 (Polychromatic418967fa.accept_9_2_6_3_1_178
  119 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 159 282
  (Polychromatic418967fa.accept_9_1_6_3_1_177 118 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 117 159 282 3 39 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 116 159 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 116 159 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 159 282
  (Polychromatic418967fa.accept_7_3_5_2_1_17 115 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 159 282 3 38 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 159 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 113 159 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 159 282 (Polychromatic418967fa.accept_9_4_6_3_1_179
  112 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 111 159 282 3 37 53 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 110 159 282
  (Polychromatic418967fa.accept_9_2_6_3_1_178 110 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 159 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 109 159 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 159 282 3 36 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 159 282 (Polychromatic418967fa.accept_9_8_6_3_1_457
  107 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 159 282
  (Polychromatic418967fa.accept_9_7_6_3_1_456 106 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 159 282 3 35 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 159 282 (Polychromatic418967fa.accept_9_5_6_3_1_40 104 159 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 159 282 (Polychromatic418967fa.accept_9_4_6_3_1_179
  103 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 159 282 3 34 53 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 159 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 101 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 159 282 (Polychromatic418967fa.accept_9_1_6_3_1_177 100 159 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 159 282 3 33 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 159 282 (Polychromatic418967fa.accept_9_8_6_3_1_457 98
  159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 159 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 97 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 159 282 3 32 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 159 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 95 159 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 159 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 94
  159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 159 282 3 31 53 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 159 282
  (Polychromatic418967fa.accept_9_2_6_3_1_178 92 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 159 282 (Polychromatic418967fa.accept_9_1_6_3_1_177 91 159 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 159 282 3 30 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 159 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 89
  159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 159 282
  (Polychromatic418967fa.accept_7_4_5_2_1_243 88 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 159 282 3 29 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 159 282 (Polychromatic418967fa.accept_9_5_6_3_1_40 86 159 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 159 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 85
  159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 159 282 3 28 53 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 159 282
  (Polychromatic418967fa.accept_9_2_6_3_1_178 83 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 159 282 (Polychromatic418967fa.accept_9_1_6_3_1_177 82 159 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 159 282 3 27 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 159 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 80
  159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 159 282
  (Polychromatic418967fa.accept_9_7_6_3_1_456 79 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 159 282 3 26 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 159 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 159 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 159 282 (Polychromatic418967fa.accept_9_4_6_3_1_179
  76 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 159 282 3 25 53 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 159 282
  (Polychromatic418967fa.accept_7_4_5_2_1_243 74 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 159 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 159 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 159 282 3 24 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 159 282 (Polychromatic418967fa.accept_9_8_6_3_1_457 71
  159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 159 282
  (Polychromatic418967fa.accept_9_7_6_3_1_456 70 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 159 282 3 23 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 159 282 (Polychromatic418967fa.accept_9_5_6_3_1_40 68 159 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 159 282 (Polychromatic418967fa.accept_7_4_5_2_1_243
  67 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 159 282 3 22 53 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 159 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 159 282 (Polychromatic418967fa.accept_9_1_6_3_1_177 64 159 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 159 282 3 21 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 159 282 (Polychromatic418967fa.accept_9_8_6_3_1_457 62
  159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 159 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 61 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 159 282 3 20 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 159 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 159 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 159 282 (Polychromatic418967fa.accept_9_4_6_3_1_179
  58 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 159 282 3 19 53 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 159 282
  (Polychromatic418967fa.accept_9_2_6_3_1_178 56 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 159 282 (Polychromatic418967fa.accept_9_1_6_3_1_177 55 159 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 159 282 3 18 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 159 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 53
  159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 159 282
  (Polychromatic418967fa.accept_7_3_5_2_1_17 52 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 159 282 3 17 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 159 282 (Polychromatic418967fa.accept_9_5_6_3_1_40 50 159 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 49
  159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 159 282 3 16 53 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 159 282
  (Polychromatic418967fa.accept_9_2_6_3_1_178 47 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 159 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 159 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 159 282 3 15 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 159 282 (Polychromatic418967fa.accept_9_8_6_3_1_457 44
  159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 282
  (Polychromatic418967fa.accept_9_7_6_3_1_456 43 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 159 282 3 14 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 159 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 159 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 159 282 (Polychromatic418967fa.accept_9_4_6_3_1_179
  40 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 159 282 3 13 53 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 159 282
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 159 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 159 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 159 282 3 12 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 159 282 (Polychromatic418967fa.accept_9_8_6_3_1_457 35
  159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 159 282
  (Polychromatic418967fa.accept_9_7_6_3_1_456 34 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 159 282 3 11 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 159 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 159 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 31
  159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 159 282 3 10 53 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 159 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 159 282 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 159 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 159 282 3 9 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 159 282 (Polychromatic418967fa.accept_9_8_6_3_1_457 26
  159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 159 282 3 8 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 159 282 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 159 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 282 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 159 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 159 282 3 7 53 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 159 282
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 159 282 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 159 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 159 282 3 6 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 159 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 282
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 159 282 3 5 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 159 282 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 159 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 159 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 159 282 3 4 53 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 159 282
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 159 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 159 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 159 282 3 3 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 159 282 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 159 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 282
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 159 282 3 2 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 159 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 159 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 159 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 159 282 3 1 53 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 159 282
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 159 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 159 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 159 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 159
  282))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 125 158 282 (Eq.refl Bool.true) (allA_succ_of_gcd 124 158 282 2 62 79 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 158 282
  (Polychromatic418967fa.accept_9_6_5_3_1_205 123 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 158 282 2 61 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 158 282 (accept_3_4 121 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 158 282 2 60 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 158 282 (Polychromatic418967fa.accept_9_2_5_3_1_37 119 158 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 158 282 2 59 79 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 158 282
  (Polychromatic418967fa.accept_7_5_4_2_1_235 117 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 158 282 2 58 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 158 282 (accept_3_4 115 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 158 282 2 57 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 158 282 (Polychromatic418967fa.accept_11_3_4_7_1_114 113 158 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 158 282 2 56 79 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 158 282
  (Polychromatic418967fa.accept_7_6_4_2_1_236 111 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 158 282 2 55 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 158 282 (accept_3_4 109 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 158 282 2 54 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 158 282 (Polychromatic418967fa.accept_9_8_5_3_1_777 107 158 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 158 282 2 53 79 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 158 282
  (Polychromatic418967fa.accept_9_6_5_3_1_205 105 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 158 282 2 52 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 158 282 (accept_3_4 103 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 158 282 2 51 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 158 282 (Polychromatic418967fa.accept_9_2_5_3_1_37 101 158 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 158 282 2 50 79 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 158 282
  (Polychromatic418967fa.accept_12_3_2_6_1_138 99 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 158 282 2 49 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 158 282 (accept_3_4 97 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 158 282 2 48 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 158 282 (Polychromatic418967fa.accept_10_5_8_2_1_517 95 158 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 158 282 2 47 79 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 158 282
  (Polychromatic418967fa.accept_12_9_2_6_1_455 93 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 158 282 2 46 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 158 282 (accept_3_4 91 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 158 282 2 45 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 158 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 89 158 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 158 282 2 44 79 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 158 282
  (Polychromatic418967fa.accept_9_6_5_3_1_205 87 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 158 282 2 43 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 158 282 (accept_3_4 85 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 158 282 2 42 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 158 282 (Polychromatic418967fa.accept_7_6_4_2_1_236 83 158 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 158 282 2 41 79 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 158 282
  (Polychromatic418967fa.accept_12_9_2_6_1_455 81 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 158 282 2 40 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 158 282 (accept_3_4 79 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 158 282 2 39 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 158 282 (Polychromatic418967fa.accept_16_13_14_10_1_1669 77 158 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 158 282 2 38 79 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 158 282
  (Polychromatic418967fa.accept_7_5_4_2_1_235 75 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 158 282 2 37 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 158 282 (accept_3_4 73 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 158 282 2 36 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 158 282 (Polychromatic418967fa.accept_9_8_5_3_1_777 71 158 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 158 282 2 35 79 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 158 282
  (Polychromatic418967fa.accept_7_6_4_2_1_236 69 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 158 282 2 34 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 158 282 (accept_3_4 67 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 158 282 2 33 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 158 282 (Polychromatic418967fa.accept_9_2_5_3_1_37 65 158 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 158 282 2 32 79 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 158 282
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 63 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 158 282 2 31 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 158 282 (accept_3_4 61 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 158 282 2 30 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 158 282 (Polychromatic418967fa.accept_13_7_2_9_1_1826 59 158 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 158 282 2 29 79 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 158 282
  (Polychromatic418967fa.accept_12_9_2_6_1_455 57 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 158 282 2 28 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 158 282 (accept_3_4 55 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 158 282 2 27 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 158 282 (Polychromatic418967fa.accept_9_8_5_3_1_777 53 158 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 158 282 2 26 79 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 158 282
  (Polychromatic418967fa.accept_9_6_5_3_1_205 51 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 158 282 2 25 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 158 282 (accept_3_4 49 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 158 282 2 24 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 158 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 158 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 158 282 2 23 79 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 158 282
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 158 282 2 22 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 158 282 (accept_3_4 43 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 158 282 2 21 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 158 282 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 158 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 158 282 2 20 79 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 158 282
  (Polychromatic418967fa.accept_12_3_2_6_1_138 39 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 158 282 2 19 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 158 282 (accept_3_4 37 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 158 282 2 18 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 158 282 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 158 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 158 282 2 17 79 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 158 282
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 158 282 2 16 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 158 282 (accept_3_4 31 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 158 282 2 15 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 158 282 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 158 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 158 282 2 14 79 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 158 282
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 158 282 2 13 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 158 282 (accept_3_4 25 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 158 282 2 12 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 158 282 (Polychromatic418967fa.accept_14_9_4_2_1_983 23 158 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 158 282 2 11 79 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 158 282
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 158 282 2 10 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 158 282 (accept_3_4 19 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 158 282 2 9 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 158 282 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 158 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 282 2 8 79 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 282
  (Polychromatic418967fa.accept_9_6_5_3_1_205 15 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 158 282 2 7 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 158 282 (accept_3_4 13 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 158 282 2 6 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 158 282 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 158 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 158 282 2 5 79 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 158 282
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 158 282 2 4 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 158 282 (accept_3_4 7 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 158
  282 2 3 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  158 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 158 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 158 282 2 2 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 158 282 (Polychromatic418967fa.accept_11_3_4_7_1_114 3 158 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 282 2 1 79 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 282 (accept_3_4 1 158 282
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  282)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 126 157 282 (Eq.refl Bool.true) (allA_succ_of_accept 125 157 282 (accept_3_5 125 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 157 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 124 157
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 157 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 123 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 157 282 (accept_3_5 122 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 157 282 (Polychromatic418967fa.accept_21_16_10_9_1_9965 121 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 120 157 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 120 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 157 282 (accept_3_5 119 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 157 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 118 157
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 157 282
  (Polychromatic418967fa.accept_7_5_3_2_1_249 117 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 157 282 (accept_3_5 116 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 157 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 115 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 157 282 (Polychromatic418967fa.accept_9_6_4_3_1_203 114 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 157 282 (accept_3_5 113 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 157 282 (Polychromatic418967fa.accept_13_8_1_9_1_1178 112 157
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 157 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 111 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 157 282 (accept_3_5 110 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 157 282 (Polychromatic418967fa.accept_9_1_4_3_1_201 109 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 157 282 (Polychromatic418967fa.accept_15_3_7_12_1_372 108 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 157 282 (accept_3_5 107 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 157 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 106 157
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 157 282
  (Polychromatic418967fa.accept_9_6_4_3_1_203 105 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 157 282 (accept_3_5 104 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 157 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 103 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 157 282 (Polychromatic418967fa.accept_13_11_1_9_1_1179 102 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 157 282 (accept_3_5 101 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 157 282 (Polychromatic418967fa.accept_9_1_4_3_1_201 100 157
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 157 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 99 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 157 282 (accept_3_5 98 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 157 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 97 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 157 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 96 157 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 157 282 (accept_3_5 95 157 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 157 282 (Polychromatic418967fa.accept_10_4_7_2_1_211 94 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 157 282
  (Polychromatic418967fa.accept_13_2_1_9_1_1174 93 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 157 282 (accept_3_5 92 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 157 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 157 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 90 157 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 157 282 (accept_3_5 89 157 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 157 282 (Polychromatic418967fa.accept_9_7_4_3_1_204 88 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 157 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 87 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 157 282 (accept_3_5 86 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 157 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 85 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 157 282 (Polychromatic418967fa.accept_10_4_7_2_1_211 84 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 157 282 (accept_3_5 83 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 157 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 82 157 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 157 282
  (Polychromatic418967fa.accept_11_4_3_7_1_828 81 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 157 282 (accept_3_5 80 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 157 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 157 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 157 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 157 282 (accept_3_5 77 157 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 157 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 76 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 157 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 157 282 (accept_3_5 74 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 157 282 (Polychromatic418967fa.accept_9_1_4_3_1_201 73 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 157 282 (Polychromatic418967fa.accept_20_12_17_2_1_8961 72 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 157 282 (accept_3_5 71 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 157 282 (Polychromatic418967fa.accept_9_7_4_3_1_204 70 157 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 157 282
  (Polychromatic418967fa.accept_7_6_3_2_1_461 69 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 157 282 (accept_3_5 68 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 157 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 157 282 (Polychromatic418967fa.accept_15_6_7_12_1_869 66 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 157 282 (accept_3_5 65 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 157 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 64 157 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 157 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 157 282 (accept_3_5 62 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 157 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 61 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 157 282 (Polychromatic418967fa.accept_9_6_4_3_1_203 60 157 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 157 282 (accept_3_5 59 157 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 157 282 (Polychromatic418967fa.accept_13_6_1_9_1_619 58 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 157 282
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 157 282 (accept_3_5 56 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 157 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 157 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 157 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 157 282 (accept_3_5 53 157 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 157 282 (Polychromatic418967fa.accept_9_7_4_3_1_204 52 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 157 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 157 282 (accept_3_5 50 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 157 282 (Polychromatic418967fa.accept_10_9_7_2_1_887 49 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 157 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 157 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 157 282 (accept_3_5 47 157 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 157 282 (Polychromatic418967fa.accept_9_1_4_3_1_201 46 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 157 282
  (Polychromatic418967fa.accept_10_5_7_2_1_516 45 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 157 282 (accept_3_5 44 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 157 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 157 282 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 157 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 157 282 (accept_3_5 41 157 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 157 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 157 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 157 282 (accept_3_5 38 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 157 282 (Polychromatic418967fa.accept_9_1_4_3_1_201 37 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 157 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 157 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 157 282 (accept_3_5 35 157 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 157 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 157 282
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 157 282 (accept_3_5 32 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 157 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 157 282 (Polychromatic418967fa.accept_16_14_13_10_1_2624 30 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 157 282 (accept_3_5 29 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 157 282 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 157 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 157 282 (accept_3_5 26 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 157 282 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 157 282 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 157 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 282 (accept_3_5 23 157 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 157 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 282
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 157 282 (accept_3_5 20 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 157 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 157 282 (Polychromatic418967fa.accept_13_5_1_9_1_618 18 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 282 (accept_3_5 17 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 282 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 157 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 282 (accept_3_5 14 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 157 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 282 (accept_3_5 11 157 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 282 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 282
  (Polychromatic418967fa.accept_10_9_7_2_1_887 9 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 282 (accept_3_5 8 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 157 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 282 (accept_3_5 5 157 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 282 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 157 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 282 (accept_3_5 2 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 157 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157
  282))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 127 156 282 (Eq.refl Bool.true) (allA_succ_of_gcd 126 156 282 6 21 26 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 156 282
  (Polychromatic418967fa.accept_15_5_6_12_1_916 125 156 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 156 282 2 62 78 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 123 156 282 3 41 52 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 122 156 282 2 61 78 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 156 282 (Polychromatic418967fa.accept_10_1_6_2_1_867 121 156
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 156 282 6 20 26 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 156 282
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 119 156 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 156 282 2 59 78 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 117 156 282 3 39 52 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 116 156 282 2 58 78 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 156 282 (Polychromatic418967fa.accept_15_10_6_12_1_1645 115
  156 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 156 282 6 19 26 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 156 282
  (Polychromatic418967fa.accept_17_11_3_10_1_2838 113 156 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 112 156 282 2 56 78 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 111 156 282 3 37 52 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 110 156 282 2 55 78 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 156 282
  (Polychromatic418967fa.accept_16_13_12_10_1_3540 109 156 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 108 156 282 6 18 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 107 156 282 (Polychromatic418967fa.accept_15_2_6_12_1_1613 107 156 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 156 282 2 53 78 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 105 156 282 3 35 52 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 156 282 2 52 78
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 156 282
  (Polychromatic418967fa.accept_23_11_18_6_1_15805 103 156 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 156 282 6 17 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 156 282 (Polychromatic418967fa.accept_10_1_6_2_1_867 101 156 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 156 282 2 50 78 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 156 282 3 33 52 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 156 282 2 49 78 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 156 282
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 97 156 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 156 282 6 16 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 156 282 (Polychromatic418967fa.accept_15_5_6_12_1_916 95 156 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 156 282 2 47 78 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 156 282 3 31 52 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 156 282 2 46 78 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 156 282
  (Polychromatic418967fa.accept_10_1_6_2_1_867 91 156 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 156 282 6 15 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 156 282 (Polychromatic418967fa.accept_22_1_2_18_1_9730 89 156 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 156 282 2 44 78 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 156 282 3 29 52 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 156 282 2 43 78 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 156 282
  (Polychromatic418967fa.accept_15_10_6_12_1_1645 85 156 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 156 282 6 14 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 156 282 (Polychromatic418967fa.accept_16_3_12_10_1_315 83 156 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 156 282 2 41 78 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 156 282 3 27 52 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 156 282 2 40 78 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 156 282
  (Polychromatic418967fa.accept_17_11_3_10_1_2838 79 156 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 156 282 6 13 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 156 282 (Polychromatic418967fa.accept_15_2_6_12_1_1613 77 156 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 156 282 2 38 78 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 156 282 3 25 52 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 156 282 2 37 78 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 156 282
  (Polychromatic418967fa.accept_22_7_2_18_1_12758 73 156 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 156 282 6 12 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 156 282 (Polychromatic418967fa.accept_10_1_6_2_1_867 71 156 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 156 282 2 35 78 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 156 282 3 23 52 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 156 282 2 34 78 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 156 282
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 67 156 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 156 282 6 11 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 156 282 (Polychromatic418967fa.accept_15_5_6_12_1_916 65 156 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 156 282 2 32 78 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 156 282 3 21 52 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 156 282 2 31 78 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 156 282
  (Polychromatic418967fa.accept_10_1_6_2_1_867 61 156 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 156 282 6 10 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 156 282 (Polychromatic418967fa.accept_16_11_12_10_1_3641 59 156 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 156 282 2 29 78 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 156 282 3 19 52 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 156 282 2 28 78 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 156 282
  (Polychromatic418967fa.accept_15_10_6_12_1_1645 55 156 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 156 282 6 9 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 156 282 (Polychromatic418967fa.accept_11_9_2_7_1_1298 53 156 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 156 282 2 26 78 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 156 282 3 17 52 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 156 282 2 25 78 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 156 282
  (Polychromatic418967fa.accept_19_11_4_16_1_9308 49 156 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 156 282 6 8 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 156 282 (Polychromatic418967fa.accept_15_2_6_12_1_1613 47 156 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 156 282 2 23 78 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 156 282 3 15 52 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 156 282 2 22 78 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 156 282
  (Polychromatic418967fa.accept_16_11_12_10_1_3641 43 156 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 156 282 6 7 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 156 282 (Polychromatic418967fa.accept_10_1_6_2_1_867 41 156 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 156 282 2 20 78 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 156 282 3 13 52 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 156 282 2 19 78 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 156 282
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 37 156 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 156 282 6 6 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 156 282 (Polychromatic418967fa.accept_15_5_6_12_1_916 35 156 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 156 282 2 17 78 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 156 282 3 11 52 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 156 282 2 16 78 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 156 282
  (Polychromatic418967fa.accept_10_1_6_2_1_867 31 156 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 156 282 6 5 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 156 282 (Polychromatic418967fa.accept_16_13_12_10_1_3540 29 156 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 156 282 2 14 78 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 156 282 3 9 52 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 156 282 2 13 78 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 156 282
  (Polychromatic418967fa.accept_15_10_6_12_1_1645 25 156 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 156 282 6 4 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 156 282 (Polychromatic418967fa.accept_22_1_2_18_1_9730 23 156 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 156 282 2 11 78 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 156 282 3 7 52 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 156 282 2 10 78 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 156 282
  (Polychromatic418967fa.accept_16_3_12_10_1_315 19 156 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 156 282 6 3 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 156 282 (Polychromatic418967fa.accept_15_2_6_12_1_1613 17 156 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 156 282 2 8 78 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 156 282 3 5 52 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 156 282 2 7 78 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 156 282
  (Polychromatic418967fa.accept_16_13_12_10_1_3540 13 156 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 156 282 6 2 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 156 282 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 156 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 156 282 2 5 78 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 156 282 3 3 52 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 156 282 2 4 78 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 156 282
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 7 156 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 156 282 6 1 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 156 282 (Polychromatic418967fa.accept_15_5_6_12_1_916 5 156 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 282 2 2 78 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 156 282 3 1 52 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 156 282 2 1 78 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 282 (Polychromatic418967fa.accept_10_1_6_2_1_867 1
  156 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  282)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 128 155 282 (Eq.refl Bool.true) (allA_succ_of_accept 127 155 282 (accept_3_4 127 155 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 155 282 (Polychromatic418967fa.accept_15_6_5_12_1_1642 126
  155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 155 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 125 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 155 282 (accept_3_4 124 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 155 282 (Polychromatic418967fa.accept_9_6_2_3_1_771 123 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 155 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 122 155 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 155 282 (accept_3_4 121 155 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 155 282 (Polychromatic418967fa.accept_13_3_12_9_1_1193 120
  155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 155 282
  (Polychromatic418967fa.accept_19_5_3_16_1_9307 119 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 118 155 282 (accept_3_4 118 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 155 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 117 155 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 155 282 (Polychromatic418967fa.accept_9_8_2_3_1_447 116 155
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 155 282 (accept_3_4 115 155
  282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 155 282
  (Polychromatic418967fa.accept_9_6_2_3_1_771 114 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 155 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 113 155 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 155 282 (accept_3_4 112 155 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 155 282 (Polychromatic418967fa.accept_7_6_1_2_1_230 111 155 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 155 282
  (Polychromatic418967fa.accept_17_8_2_10_1_2879 110 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 155 282 (accept_3_4 109 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 155 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 108 155 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 155 282 (Polychromatic418967fa.accept_9_8_2_3_1_447 107 155
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 155 282 (accept_3_4 106 155
  282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 155 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 105 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 155 282 (Polychromatic418967fa.accept_7_6_1_2_1_230 104 155 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 155 282 (accept_3_4 103 155 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 155 282 (Polychromatic418967fa.accept_21_18_8_9_1_2457 102 155 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 155 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 101 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 155 282 (accept_3_4 100 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 155 282 (Polychromatic418967fa.accept_13_8_12_9_1_1168 99 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 155 282 (Polychromatic418967fa.accept_9_8_2_3_1_447 98 155 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 155 282 (accept_3_4 97 155 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 155 282 (Polychromatic418967fa.accept_9_6_2_3_1_771 96 155 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 155 282
  (Polychromatic418967fa.accept_9_5_2_3_1_194 95 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 155 282 (accept_3_4 94 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 155 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 155 282 (Polychromatic418967fa.accept_14_8_1_2_1_965 92 155 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 155 282 (accept_3_4 91 155 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 155 282 (Polychromatic418967fa.accept_7_6_1_2_1_230 90 155 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 155 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 155 282 (accept_3_4 88 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 155 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 87 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 155 282 (Polychromatic418967fa.accept_9_5_2_3_1_194 86 155 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 155 282 (accept_3_4 85 155 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 155 282 (Polychromatic418967fa.accept_15_9_5_12_1_1640 84 155 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 155 282
  (Polychromatic418967fa.accept_7_6_1_2_1_230 83 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 155 282 (accept_3_4 82 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 155 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 155 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 80 155 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 155 282 (accept_3_4 79 155 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 155 282 (Polychromatic418967fa.accept_9_6_2_3_1_771 78 155 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 155 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 155 282 (accept_3_4 76 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 155 282 (Polychromatic418967fa.accept_13_10_12_9_1_1837 75 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 155 282 (Polychromatic418967fa.accept_19_17_3_16_1_13384 74 155 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 155 282 (accept_3_4 73 155 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 155 282 (Polychromatic418967fa.accept_11_6_1_7_1_1315 72 155
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 155 282
  (Polychromatic418967fa.accept_9_8_2_3_1_447 71 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 155 282 (accept_3_4 70 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 155 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 155 282 (Polychromatic418967fa.accept_9_5_2_3_1_194 68 155 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 155 282 (accept_3_4 67 155 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 155 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 155 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 155 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 155 282 (accept_3_4 64 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 155 282 (Polychromatic418967fa.accept_10_3_5_2_1_38 63 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 155 282 (Polychromatic418967fa.accept_7_6_1_2_1_230 62 155 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 155 282 (accept_3_4 61 155 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 155 282 (Polychromatic418967fa.accept_9_6_2_3_1_771 60 155 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 155 282
  (Polychromatic418967fa.accept_7_3_1_2_1_247 59 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 155 282 (accept_3_4 58 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 155 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 155 282 (Polychromatic418967fa.accept_19_18_3_16_1_7962 56 155 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 155 282 (accept_3_4 55 155 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 155 282 (Polychromatic418967fa.accept_15_9_5_12_1_1640 54 155
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 155 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 155 282 (accept_3_4 52 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 155 282 (Polychromatic418967fa.accept_9_6_2_3_1_771 51 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 155 282 (Polychromatic418967fa.accept_9_5_2_3_1_194 50 155 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 155 282 (accept_3_4 49 155 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 155 282 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 155 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 155 282
  (Polychromatic418967fa.accept_10_7_5_2_1_880 47 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 155 282 (accept_3_4 46 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 155 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 155 282 (Polychromatic418967fa.accept_9_8_2_3_1_447 44 155 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 155 282 (accept_3_4 43 155 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 155 282 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 155 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 155 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 155 282 (accept_3_4 40 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 155 282 (Polychromatic418967fa.accept_11_6_1_7_1_1315 39 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 155 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 38 155 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 155 282 (accept_3_4 37 155 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 155 282 (Polychromatic418967fa.accept_13_10_12_9_1_1837 36 155 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 155 282
  (Polychromatic418967fa.accept_9_8_2_3_1_447 35 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 155 282 (accept_3_4 34 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 155 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 155 282 (Polychromatic418967fa.accept_9_5_2_3_1_194 32 155 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 155 282 (accept_3_4 31 155 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 155 282 (Polychromatic418967fa.accept_20_10_15_2_1_3132 30 155 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 155 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 155 282 (accept_3_4 28 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 155 282 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 155 282 (Polychromatic418967fa.accept_9_8_2_3_1_447 26 155 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 155 282 (accept_3_4 25 155 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 155 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 155 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 155 282
  (Polychromatic418967fa.accept_9_5_2_3_1_194 23 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 155 282 (accept_3_4 22 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 155 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 155 282 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 155 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 155 282 (accept_3_4 19 155 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 282 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 155 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 155 282 (accept_3_4 16 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 155 282 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 155 282 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 155 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 155 282 (accept_3_4 13 155 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 155 282 (Polychromatic418967fa.accept_16_12_11_10_1_1667 12 155 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 282
  (Polychromatic418967fa.accept_22_11_1_18_1_12787 11 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 155 282 (accept_3_4 10 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 155 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 155 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 282 (Polychromatic418967fa.accept_9_8_2_3_1_447 8 155 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 282 (accept_3_4 7 155 282
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 155 282 (Polychromatic418967fa.accept_7_6_1_2_1_230 6
  155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 155 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 155 282 (accept_3_4 4 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  155 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 155 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 155 282 (Polychromatic418967fa.accept_15_2_5_12_1_369 2 155 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 282 (accept_3_4 1 155 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 155
  282))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 129 154 282 (Eq.refl Bool.true) (allA_succ_of_gcd 128 154 282 2 64 77 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 154 282
  (Polychromatic418967fa.accept_10_7_4_2_1_903 127 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 154 282 2 63 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 154 282 (accept_3_5 125 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 154 282 2 62 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 154 282 (Polychromatic418967fa.accept_9_6_1_3_1_191 123 154 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 154 282 2 61 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 154 282
  (Polychromatic418967fa.accept_9_4_1_3_1_190 121 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 154 282 2 60 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 154 282 (accept_3_5 119 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 154 282 2 59 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 154 282 (Polychromatic418967fa.accept_10_7_4_2_1_903 117 154 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 154 282 2 58 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 154 282
  (Polychromatic418967fa.accept_9_7_1_3_1_443 115 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 154 282 2 57 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 154 282 (accept_3_5 113 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 154 282 2 56 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 154 282 (Polychromatic418967fa.accept_12_3_10_6_1_442 111 154 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 154 282 2 55 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 154 282
  (Polychromatic418967fa.accept_17_7_1_10_1_2836 109 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 108 154 282 2 54 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 107 154 282 (accept_3_5 107 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 154 282 2 53 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 154 282 (Polychromatic418967fa.accept_9_6_1_3_1_191 105 154 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 154 282 2 52 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 154 282
  (Polychromatic418967fa.accept_9_4_1_3_1_190 103 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 154 282 2 51 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 154 282 (accept_3_5 101 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 154 282 2 50 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 154 282 (Polychromatic418967fa.accept_12_3_10_6_1_442 99 154 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 154 282 2 49 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 154 282
  (Polychromatic418967fa.accept_9_7_1_3_1_443 97 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 154 282 2 48 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 154 282 (accept_3_5 95 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 154 282 2 47 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 154 282 (Polychromatic418967fa.accept_12_9_10_6_1_872 93 154 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 154 282 2 46 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 154 282
  (Polychromatic418967fa.accept_15_1_4_12_1_2401 91 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 154 282 2 45 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 154 282 (accept_3_5 89 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 154 282 2 44 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 154 282 (Polychromatic418967fa.accept_9_6_1_3_1_191 87 154 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 154 282 2 43 77 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 154 282
  (Polychromatic418967fa.accept_9_4_1_3_1_190 85 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 154 282 2 42 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 154 282 (accept_3_5 83 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 154 282 2 41 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 154 282 (Polychromatic418967fa.accept_12_9_10_6_1_872 81 154 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 154 282 2 40 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 154 282
  (Polychromatic418967fa.accept_9_7_1_3_1_443 79 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 154 282 2 39 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 154 282 (accept_3_5 77 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 154 282 2 38 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 154 282 (Polychromatic418967fa.accept_12_3_10_6_1_442 75 154 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 154 282 2 37 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 154 282
  (Polychromatic418967fa.accept_13_8_11_9_1_593 73 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 154 282 2 36 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 154 282 (accept_3_5 71 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 154 282 2 35 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 154 282 (Polychromatic418967fa.accept_9_6_1_3_1_191 69 154 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 154 282 2 34 77 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 154 282
  (Polychromatic418967fa.accept_9_4_1_3_1_190 67 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 154 282 2 33 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 154 282 (accept_3_5 65 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 154 282 2 32 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 154 282 (Polychromatic418967fa.accept_12_3_10_6_1_442 63 154 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 154 282 2 31 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 154 282
  (Polychromatic418967fa.accept_9_7_1_3_1_443 61 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 154 282 2 30 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 154 282 (accept_3_5 59 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 154 282 2 29 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 154 282 (Polychromatic418967fa.accept_10_7_4_2_1_903 57 154 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 154 282 2 28 77 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 154 282
  (Polychromatic418967fa.accept_19_17_2_16_1_7982 55 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 154 282 2 27 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 154 282 (accept_3_5 53 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 154 282 2 26 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 154 282 (Polychromatic418967fa.accept_9_6_1_3_1_191 51 154 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 154 282 2 25 77 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 154 282
  (Polychromatic418967fa.accept_9_4_1_3_1_190 49 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 154 282 2 24 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 154 282 (accept_3_5 47 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 154 282 2 23 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 154 282 (Polychromatic418967fa.accept_12_9_10_6_1_872 45 154 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 154 282 2 22 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 154 282
  (Polychromatic418967fa.accept_9_7_1_3_1_443 43 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 154 282 2 21 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 154 282 (accept_3_5 41 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 154 282 2 20 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 154 282 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 154 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 154 282 2 19 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 154 282
  (Polychromatic418967fa.accept_10_7_4_2_1_903 37 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 154 282 2 18 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 154 282 (accept_3_5 35 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 154 282 2 17 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 154 282 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 154 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 154 282 2 16 77 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 154 282
  (Polychromatic418967fa.accept_9_4_1_3_1_190 31 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 154 282 2 15 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 154 282 (accept_3_5 29 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 154 282 2 14 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 154 282 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 154 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 154 282 2 13 77 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 154 282
  (Polychromatic418967fa.accept_9_7_1_3_1_443 25 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 154 282 2 12 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 154 282 (accept_3_5 23 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 154 282 2 11 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 154 282 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 154 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 154 282 2 10 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 154 282
  (Polychromatic418967fa.accept_21_19_7_9_1_11487 19 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 154 282 2 9 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 154 282 (accept_3_5 17 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 154 282 2 8 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 154 282 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 154 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 154 282 2 7 77 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 154 282
  (Polychromatic418967fa.accept_9_4_1_3_1_190 13 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 154 282 2 6 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 154 282 (accept_3_5 11 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 154 282 2 5 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 154 282 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 154 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 154 282 2 4 77 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 154 282
  (Polychromatic418967fa.accept_9_7_1_3_1_443 7 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 154 282 2 3 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 154 282 (accept_3_5 5 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 154
  282 2 2 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  154 282 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 154 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 154 282 2 1 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 154 282 (Polychromatic418967fa.accept_13_1_11_9_1_1857 1 154 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154
  282)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 130 153 282 (Eq.refl Bool.true) (allA_succ_of_gcd 129 153 282 3 43 51 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 128 153 282
  (Polychromatic418967fa.accept_12_8_9_6_1_127 128 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 127 153 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 127 153 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 153 282 3 42 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 153 282 (Polychromatic418967fa.accept_10_5_3_2_1_899
  125 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 153 282
  (Polychromatic418967fa.accept_11_3_10_7_1_129 124 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 123 153 282 3 41 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 122 153 282 (Polychromatic418967fa.accept_7_3_6_2_1_90 122 153 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 153 282 (Polychromatic418967fa.accept_10_1_3_2_1_220
  121 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 153 282 3 40 51 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 153 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 119 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 153 282 (Polychromatic418967fa.accept_12_10_9_6_1_1445 118 153 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 117 153 282 3 39 51 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 116 153 282
  (Polychromatic418967fa.accept_7_4_6_2_1_451 116 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 153 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 115 153 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 153 282 3 38 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 153 282 (Polychromatic418967fa.accept_7_1_6_2_1_18
  113 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 153 282
  (Polychromatic418967fa.accept_12_4_9_6_1_440 112 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 111 153 282 3 37 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 110 153 282 (Polychromatic418967fa.accept_12_2_9_6_1_439 110 153 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 153 282
  (Polychromatic418967fa.accept_7_4_6_2_1_451 109 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 153 282 3 36 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 153 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 107 153 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 153 282 (Polychromatic418967fa.accept_7_1_6_2_1_18
  106 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 153 282 3 35 51 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 153 282
  (Polychromatic418967fa.accept_12_8_9_6_1_127 104 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 153 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 103 153 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 153 282 3 34 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 153 282 (Polychromatic418967fa.accept_7_3_6_2_1_90
  101 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 153 282
  (Polychromatic418967fa.accept_12_4_9_6_1_440 100 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 153 282 3 33 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 153 282 (Polychromatic418967fa.accept_12_2_9_6_1_439 98 153 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 153 282
  (Polychromatic418967fa.accept_13_6_10_9_1_4329 97 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 153 282 3 32 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 153 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 95 153 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 153 282 (Polychromatic418967fa.accept_7_3_6_2_1_90 94
  153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 153 282 3 31 51 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 153 282
  (Polychromatic418967fa.accept_7_1_6_2_1_18 92 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 153 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 153 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 153 282 3 30 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 153 282
  (Polychromatic418967fa.accept_18_17_9_12_1_2160 89 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 153 282 (Polychromatic418967fa.accept_7_4_6_2_1_451 88 153 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 153 282 3 29 51 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 153 282
  (Polychromatic418967fa.accept_12_2_9_6_1_439 86 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 153 282 (Polychromatic418967fa.accept_7_1_6_2_1_18 85 153 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 153 282 3 28 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 153 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 83
  153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 153 282
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 82 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 153 282 3 27 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 153 282 (Polychromatic418967fa.accept_7_3_6_2_1_90 80 153 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 153 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 79
  153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 153 282 3 26 51 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 153 282
  (Polychromatic418967fa.accept_13_12_10_9_1_1166 77 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 153 282 (Polychromatic418967fa.accept_12_4_9_6_1_440 76 153 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 153 282 3 25 51 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 153 282
  (Polychromatic418967fa.accept_7_4_6_2_1_451 74 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 153 282 (Polychromatic418967fa.accept_7_3_6_2_1_90 73 153 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 153 282 3 24 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 153 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 71
  153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 153 282
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 70 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 153 282 3 23 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 153 282 (Polychromatic418967fa.accept_12_8_9_6_1_127 68 153 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 153 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 67
  153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 153 282 3 22 51 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 153 282
  (Polychromatic418967fa.accept_10_5_3_2_1_899 65 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 153 282 (Polychromatic418967fa.accept_7_1_6_2_1_18 64 153 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 153 282 3 21 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 153 282 (Polychromatic418967fa.accept_12_2_9_6_1_439
  62 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 153 282
  (Polychromatic418967fa.accept_10_1_3_2_1_220 61 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 153 282 3 20 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 153 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 153 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 282 (Polychromatic418967fa.accept_11_3_10_7_1_129
  58 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 153 282 3 19 51 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 153 282
  (Polychromatic418967fa.accept_12_8_9_6_1_127 56 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 153 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 153 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 153 282 3 18 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 153 282 (Polychromatic418967fa.accept_7_4_6_2_1_451 53
  153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 282
  (Polychromatic418967fa.accept_7_3_6_2_1_90 52 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 153 282 3 17 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 153 282 (Polychromatic418967fa.accept_7_1_6_2_1_18 50 153 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 153 282
  (Polychromatic418967fa.accept_16_1_9_10_1_4740 49 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 153 282 3 16 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 153 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 153 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 282 (Polychromatic418967fa.accept_7_4_6_2_1_451
  46 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 153 282 3 15 51 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 153 282
  (Polychromatic418967fa.accept_12_8_9_6_1_127 44 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 153 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 153 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 153 282 3 14 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 153 282 (Polychromatic418967fa.accept_10_1_3_2_1_220
  41 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 282
  (Polychromatic418967fa.accept_12_4_9_6_1_440 40 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 153 282 3 13 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 153 282 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 153 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 282 (Polychromatic418967fa.accept_15_7_3_12_1_365
  37 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 153 282 3 12 51 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 153 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 153 282 (Polychromatic418967fa.accept_12_10_9_6_1_1445 34 153 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 153 282 3 11 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 153 282 (Polychromatic418967fa.accept_7_4_6_2_1_451 32
  153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 31 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 153 282 3 10 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 153 282 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 153 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 282 (Polychromatic418967fa.accept_12_4_9_6_1_440
  28 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 153 282 3 9 51 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 153 282
  (Polychromatic418967fa.accept_12_2_9_6_1_439 26 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 153 282 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 153 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 153 282 3 8 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 153 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 23
  153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 282
  (Polychromatic418967fa.accept_7_1_6_2_1_18 22 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 153 282 3 7 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 153 282 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 153 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 153 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 153 282 3 6 51 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 153 282
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 153 282 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 153 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 153 282 3 5 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 153 282 (Polychromatic418967fa.accept_11_3_10_7_1_129
  14 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 282
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 153 282 3 4 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 153 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 153 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 282
  (Polychromatic418967fa.accept_7_3_6_2_1_90 10 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 153 282 3 3 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 153 282 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 153 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 153 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 153 282 3 2 51 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 153 282
  (Polychromatic418967fa.accept_10_5_3_2_1_899 5 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 153 282 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 153 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 153 282 3 1 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 153 282 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 153 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 282
  (Polychromatic418967fa.accept_7_1_6_2_1_18 1 153 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 153
  282))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 131 152 282 (Eq.refl Bool.true) (allA_succ_of_gcd 130 152 282 2 65 76 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 129 152 282
  (Polychromatic418967fa.accept_7_3_5_2_1_17 129 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 128 152 282 2 64 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 127 152 282 (accept_3_4 127 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 152 282 2 63 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 152 282 (Polychromatic418967fa.accept_15_5_2_12_1_2543 125 152 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 152 282 2 62 76 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 152 282
  (Polychromatic418967fa.accept_7_4_5_2_1_243 123 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 152 282 2 61 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 152 282 (accept_3_4 121 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 152 282 2 60 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 152 282 (Polychromatic418967fa.accept_9_2_8_3_1_181 119 152 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 152 282 2 59 76 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 152 282
  (Polychromatic418967fa.accept_12_9_8_6_1_466 117 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 152 282 2 58 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 152 282 (accept_3_4 115 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 152 282 2 57 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 152 282 (Polychromatic418967fa.accept_9_5_8_3_1_437 113 152 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 152 282 2 56 76 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 152 282
  (Polychromatic418967fa.accept_12_3_8_6_1_895 111 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 152 282 2 55 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 152 282 (accept_3_4 109 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 152 282 2 54 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 152 282 (Polychromatic418967fa.accept_20_7_12_2_1_4465 107 152 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 152 282 2 53 76 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 152 282
  (Polychromatic418967fa.accept_9_6_8_3_1_183 105 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 152 282 2 52 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 152 282 (accept_3_4 103 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 152 282 2 51 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 152 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 101 152 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 152 282 2 50 76 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 152 282
  (Polychromatic418967fa.accept_12_3_8_6_1_895 99 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 152 282 2 49 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 152 282 (accept_3_4 97 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 152 282 2 48 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 152 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 95 152 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 152 282 2 47 76 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 152 282
  (Polychromatic418967fa.accept_11_5_9_7_1_411 93 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 152 282 2 46 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 152 282 (accept_3_4 91 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 152 282 2 45 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 152 282 (Polychromatic418967fa.accept_15_14_2_12_1_2472 89 152 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 152 282 2 44 76 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 152 282
  (Polychromatic418967fa.accept_7_3_5_2_1_17 87 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 152 282 2 43 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 152 282 (accept_3_4 85 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 152 282 2 42 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 152 282 (Polychromatic418967fa.accept_9_2_8_3_1_181 83 152 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 152 282 2 41 76 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 152 282
  (Polychromatic418967fa.accept_7_4_5_2_1_243 81 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 152 282 2 40 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 152 282 (accept_3_4 79 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 152 282 2 39 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 152 282 (Polychromatic418967fa.accept_9_5_8_3_1_437 77 152 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 152 282 2 38 76 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 152 282
  (Polychromatic418967fa.accept_12_3_8_6_1_895 75 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 152 282 2 37 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 152 282 (accept_3_4 73 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 152 282 2 36 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 152 282 (Polychromatic418967fa.accept_11_5_9_7_1_411 71 152 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 152 282 2 35 76 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 152 282
  (Polychromatic418967fa.accept_9_6_8_3_1_183 69 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 152 282 2 34 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 152 282 (accept_3_4 67 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 152 282 2 33 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 152 282 (Polychromatic418967fa.accept_9_2_8_3_1_181 65 152 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 152 282 2 32 76 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 152 282
  (Polychromatic418967fa.accept_12_3_8_6_1_895 63 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 152 282 2 31 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 152 282 (accept_3_4 61 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 152 282 2 30 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 152 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 152 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 152 282 2 29 76 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 152 282
  (Polychromatic418967fa.accept_11_2_9_7_1_124 57 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 152 282 2 28 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 152 282 (accept_3_4 55 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 152 282 2 27 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 152 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 152 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 152 282 2 26 76 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 152 282
  (Polychromatic418967fa.accept_9_6_8_3_1_183 51 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 152 282 2 25 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 152 282 (accept_3_4 49 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 152 282 2 24 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 152 282 (Polychromatic418967fa.accept_9_2_8_3_1_181 47 152 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 152 282 2 23 76 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 152 282
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 152 282 2 22 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 152 282 (accept_3_4 43 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 152 282 2 21 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 152 282 (Polychromatic418967fa.accept_9_5_8_3_1_437 41 152 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 152 282 2 20 76 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 152 282
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 152 282 2 19 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 152 282 (accept_3_4 37 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 152 282 2 18 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 152 282 (Polychromatic418967fa.accept_11_2_9_7_1_124 35 152 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 152 282 2 17 76 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 152 282
  (Polychromatic418967fa.accept_9_6_8_3_1_183 33 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 152 282 2 16 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 152 282 (accept_3_4 31 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 152 282 2 15 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 152 282 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 152 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 152 282 2 14 76 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 152 282
  (Polychromatic418967fa.accept_11_5_9_7_1_411 27 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 152 282 2 13 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 152 282 (accept_3_4 25 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 152 282 2 12 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 152 282 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 152 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 152 282 2 11 76 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 152 282
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 152 282 2 10 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 152 282 (accept_3_4 19 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 152 282 2 9 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 152 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 152 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 152 282 2 8 76 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 152 282
  (Polychromatic418967fa.accept_9_6_8_3_1_183 15 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 152 282 2 7 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 152 282 (accept_3_4 13 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 152 282 2 6 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 152 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 152 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 152 282 2 5 76 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 152 282
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 152 282 2 4 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 152 282 (accept_3_4 7 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 152
  282 2 3 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  152 282 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 152 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 152 282 2 2 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 152 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 152 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 152 282 2 1 76 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 152 282 (accept_3_4 1 152 282
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  282)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 132 151 282 (Eq.refl Bool.true) (allA_succ_of_accept 131 151 282 (accept_3_5 131 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 151 282 (Polychromatic418967fa.accept_9_4_7_3_1_43 130 151
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 151 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 129 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 128 151 282 (accept_3_5 128 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  127 151 282 (Polychromatic418967fa.accept_9_1_7_3_1_41 127 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 126 151 282 (Polychromatic418967fa.accept_10_6_1_2_1_874 126 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 151 282 (accept_3_5 125 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 151 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 124 151
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 151 282
  (Polychromatic418967fa.accept_9_6_7_3_1_436 123 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 151 282 (accept_3_5 122 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 151 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 121 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 151 282 (Polychromatic418967fa.accept_13_3_8_9_1_1134 120 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 151 282 (accept_3_5 119 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 151 282 (Polychromatic418967fa.accept_7_6_4_2_1_236 118 151
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 151 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 117 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 151 282 (accept_3_5 116 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 151 282 (Polychromatic418967fa.accept_13_11_8_9_1_1161 115 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 114 151 282 (Polychromatic418967fa.accept_9_6_7_3_1_436 114 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 151 282 (accept_3_5 113 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 151 282 (Polychromatic418967fa.accept_9_4_7_3_1_43 112 151
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 151 282
  (Polychromatic418967fa.accept_7_6_4_2_1_236 111 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 151 282 (accept_3_5 110 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 151 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 109 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 151 282 (Polychromatic418967fa.accept_13_4_8_9_1_1156 108 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 151 282 (accept_3_5 107 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 151 282 (Polychromatic418967fa.accept_10_6_1_2_1_874 106 151
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 151 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 105 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 151 282 (accept_3_5 104 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 151 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 103 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 151 282 (Polychromatic418967fa.accept_13_11_8_9_1_1161 102 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 151 282 (accept_3_5 101 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 151 282 (Polychromatic418967fa.accept_9_1_7_3_1_41 100 151
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 151 282
  (Polychromatic418967fa.accept_10_9_1_2_1_522 99 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 151 282 (accept_3_5 98 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 151 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 151 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 96 151 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 151 282 (accept_3_5 95 151 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 151 282 (Polychromatic418967fa.accept_9_4_7_3_1_43 94 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 151 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 93 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 151 282 (accept_3_5 92 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 151 282 (Polychromatic418967fa.accept_9_1_7_3_1_41 91 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 151 282 (Polychromatic418967fa.accept_7_6_4_2_1_236 90 151 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 151 282 (accept_3_5 89 151 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 151 282 (Polychromatic418967fa.accept_15_13_1_12_1_1638 88 151 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 151 282
  (Polychromatic418967fa.accept_9_6_7_3_1_436 87 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 151 282 (accept_3_5 86 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 151 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 151 282 (Polychromatic418967fa.accept_19_8_18_16_1_7937 84 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 151 282 (accept_3_5 83 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 151 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 82 151 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 151 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 151 282 (accept_3_5 80 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 151 282 (Polychromatic418967fa.accept_10_9_1_2_1_522 79 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 151 282 (Polychromatic418967fa.accept_9_6_7_3_1_436 78 151 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 151 282 (accept_3_5 77 151 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 151 282 (Polychromatic418967fa.accept_7_6_4_2_1_236 76 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 151 282
  (Polychromatic418967fa.accept_7_5_4_2_1_235 75 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 151 282 (accept_3_5 74 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 151 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 151 282 (Polychromatic418967fa.accept_13_7_8_9_1_1158 72 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 151 282 (accept_3_5 71 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 151 282 (Polychromatic418967fa.accept_11_4_8_7_1_819 70 151
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 151 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 151 282 (accept_3_5 68 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 151 282 (Polychromatic418967fa.accept_9_4_7_3_1_43 67 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 151 282 (Polychromatic418967fa.accept_10_6_1_2_1_874 66 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 151 282 (accept_3_5 65 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 151 282 (Polychromatic418967fa.accept_9_1_7_3_1_41 64 151 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 151 282
  (Polychromatic418967fa.accept_10_3_1_2_1_521 63 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 151 282 (accept_3_5 62 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 151 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 151 282 (Polychromatic418967fa.accept_9_6_7_3_1_436 60 151 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 151 282 (accept_3_5 59 151 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 151 282 (Polychromatic418967fa.accept_9_4_7_3_1_43 58 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 151 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 151 282 (accept_3_5 56 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 151 282 (Polychromatic418967fa.accept_7_6_4_2_1_236 55 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 151 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 151 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 151 282 (accept_3_5 53 151 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 151 282 (Polychromatic418967fa.accept_19_14_18_16_1_6530 52 151 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 151 282
  (Polychromatic418967fa.accept_9_6_7_3_1_436 51 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 151 282 (accept_3_5 50 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 151 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 151 282 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 151 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 151 282 (accept_3_5 47 151 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 151 282 (Polychromatic418967fa.accept_9_1_7_3_1_41 46 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 151 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 151 282 (accept_3_5 44 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 151 282 (Polychromatic418967fa.accept_10_3_1_2_1_521 43 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 151 282 (Polychromatic418967fa.accept_9_6_7_3_1_436 42 151 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 151 282 (accept_3_5 41 151 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 151 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 151 282
  (Polychromatic418967fa.accept_10_9_1_2_1_522 39 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 151 282 (accept_3_5 38 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 151 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 151 282 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 151 282 (accept_3_5 35 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 151 282 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 151 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 151 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 151 282 (accept_3_5 32 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 151 282 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 151 282 (Polychromatic418967fa.accept_13_4_8_9_1_1156 30 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 151 282 (accept_3_5 29 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 151 282 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 151 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 151 282
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 151 282 (accept_3_5 26 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 151 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 151 282 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 151 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 151 282 (accept_3_5 23 151 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 151 282 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 151 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 151 282 (accept_3_5 20 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 151 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 151 282 (Polychromatic418967fa.accept_21_18_4_9_1_8484 18 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 282 (accept_3_5 17 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 151 282 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 151
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 282
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 151 282 (accept_3_5 14 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 151 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 151 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 151 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 282 (accept_3_5 11 151 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 151 282 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 151 282 (accept_3_5 8 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  151 282 (Polychromatic418967fa.accept_13_7_8_9_1_1158 7 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 151 282 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 151 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 282 (accept_3_5 5 151 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 282 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 151 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 282
  (Polychromatic418967fa.accept_10_3_1_2_1_521 3 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 282 (accept_3_5 2 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 151 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151
  282))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 133 150 282 (Eq.refl Bool.true) (allA_succ_of_gcd 132 150 282 6 22 25 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 131 150 282
  (Polychromatic418967fa.accept_7_5_3_2_1_249 131 150 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 130 150 282 2 65 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 129 150 282 3 43 50 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 128 150 282 2 64 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 150 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 127 150 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 150 282 6 21 25 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 150 282
  (Polychromatic418967fa.accept_7_6_3_2_1_461 125 150 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 150 282 2 62 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 123 150 282 3 41 50 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 122 150 282 2 61 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 150 282 (Polychromatic418967fa.accept_9_4_6_3_1_179 121 150
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 150 282 6 20 25 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 150 282
  (Polychromatic418967fa.accept_9_2_6_3_1_178 119 150 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 150 282 2 59 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 117 150 282 3 39 50 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 116 150 282 2 58 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 150 282 (Polychromatic418967fa.accept_9_7_6_3_1_456 115 150
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 150 282 6 19 25 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 150 282
  (Polychromatic418967fa.accept_7_1_3_2_1_13 113 150 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 150 282 2 56 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 111 150 282 3 37 50 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 110 150 282 2 55 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 150 282 (Polychromatic418967fa.accept_9_1_6_3_1_177 109 150
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 150 282 6 18 25 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 150 282
  (Polychromatic418967fa.accept_9_8_6_3_1_457 107 150 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 150 282 2 53 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 105 150 282 3 35 50 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 104 150 282 2 52 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 150 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 103 150
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 150 282 6 17 25 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 150 282
  (Polychromatic418967fa.accept_9_2_6_3_1_178 101 150 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 150 282 2 50 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 99 150 282 3 33 50 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 98 150 282 2 49 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 150 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 97 150 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 150 282 6 16 25 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 150 282
  (Polychromatic418967fa.accept_9_5_6_3_1_40 95 150 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 150 282 2 47 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 93 150 282 3 31 50 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 92 150 282 2 46 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 150 282 (Polychromatic418967fa.accept_9_1_6_3_1_177 91 150 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 150 282 6 15 25 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 150 282
  (Polychromatic418967fa.accept_7_5_3_2_1_249 89 150 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 150 282 2 44 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 87 150 282 3 29 50 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 86 150 282 2 43 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 150 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 85 150 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 150 282 6 14 25 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 150 282
  (Polychromatic418967fa.accept_7_6_3_2_1_461 83 150 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 150 282 2 41 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 150 282 3 27 50 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 80 150 282 2 40 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 150 282 (Polychromatic418967fa.accept_9_7_6_3_1_456 79 150 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 150 282 6 13 25 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 150 282
  (Polychromatic418967fa.accept_9_5_6_3_1_40 77 150 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 150 282 2 38 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 150 282 3 25 50 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 150 282 2 37 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 150 282 (Polychromatic418967fa.accept_9_1_6_3_1_177 73 150 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 150 282 6 12 25 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 150 282
  (Polychromatic418967fa.accept_7_1_3_2_1_13 71 150 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 150 282 2 35 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 150 282 3 23 50 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 150 282 2 34 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 150 282 (Polychromatic418967fa.accept_9_4_6_3_1_179 67 150 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 150 282 6 11 25 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 150 282
  (Polychromatic418967fa.accept_9_2_6_3_1_178 65 150 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 150 282 2 32 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 150 282 3 21 50 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 62 150 282 2 31 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 150 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 61 150 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 150 282 6 10 25 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 150 282
  (Polychromatic418967fa.accept_9_5_6_3_1_40 59 150 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 150 282 2 29 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 57 150 282 3 19 50 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 56 150 282 2 28 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 150 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 55 150 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 150 282 6 9 25 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 150 282
  (Polychromatic418967fa.accept_9_8_6_3_1_457 53 150 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 150 282 2 26 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 150 282 3 17 50 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 150 282 2 25 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 150 282 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 150 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 150 282 6 8 25 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 150 282
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 150 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 150 282 2 23 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 150 282 3 15 50 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 150 282 2 22 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 150 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 150 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 150 282 6 7 25 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 150 282
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 150 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 150 282 2 20 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 150 282 3 13 50 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 150 282 2 19 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 150 282 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 150 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 150 282 6 6 25 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 150 282
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 150 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 150 282 2 17 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 150 282 3 11 50 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 150 282 2 16 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 150 282 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 150 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 150 282 6 5 25 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 150 282
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 150 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 150 282 2 14 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 150 282 3 9 50 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 150 282 2 13 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 150 282 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 150 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 150 282 6 4 25 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 150 282
  (Polychromatic418967fa.accept_9_5_6_3_1_40 23 150 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 150 282 2 11 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 150 282 3 7 50 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 150 282 2 10 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 150 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 150 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 150 282 6 3 25 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 150 282
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 150 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 150 282 2 8 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 150 282 3 5 50 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 150 282 2 7 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 150 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 150 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 282 6 2 25 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 282
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 150 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 150 282 2 5 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 150 282 3 3 50 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 150 282 2 4 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 150 282 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 150 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 282 6 1 25 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 150 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 5
  150 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 150 282 2 2 75 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 150 282 3 1 50 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 150 282 2 1 75 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 282
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 150 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 150
  282)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 134 149 282 (Eq.refl Bool.true) (allA_succ_of_accept 133 149 282 (accept_3_4 133 149 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 149 282 (Polychromatic418967fa.accept_9_6_5_3_1_205 132 149
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 149 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 131 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 130 149 282 (accept_3_4 130 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  129 149 282 (Polychromatic418967fa.accept_15_9_14_12_1_913 129 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 128 149 282 (Polychromatic418967fa.accept_9_2_5_3_1_37 128 149 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 149 282 (accept_3_4 127 149 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 149 282 (Polychromatic418967fa.accept_16_14_5_10_1_3622 126
  149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 149 282
  (Polychromatic418967fa.accept_9_8_5_3_1_777 125 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 149 282 (accept_3_4 124 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 149 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 123 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 149 282 (Polychromatic418967fa.accept_11_1_6_7_1_116 122 149 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 149 282 (accept_3_4 121 149 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 149 282 (Polychromatic418967fa.accept_13_3_6_9_1_1150 120 149
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 149 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 119 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 149 282 (accept_3_4 118 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 149 282 (Polychromatic418967fa.accept_10_7_9_2_1_1887 117 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 149 282 (Polychromatic418967fa.accept_9_8_5_3_1_777 116 149 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 149 282 (accept_3_4 115 149 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 149 282 (Polychromatic418967fa.accept_9_6_5_3_1_205 114 149
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 149 282
  (Polychromatic418967fa.accept_20_13_9_2_1_5933 113 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 149 282 (accept_3_4 112 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 149 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 111 149 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 149 282 (Polychromatic418967fa.accept_9_2_5_3_1_37 110 149
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 149 282 (accept_3_4 109 149
  282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 149 282
  (Polychromatic418967fa.accept_13_4_6_9_1_3401 108 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 149 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 107 149 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 149 282 (accept_3_4 106 149 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 149 282 (Polychromatic418967fa.accept_9_6_5_3_1_205 105 149 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 149 282
  (Polychromatic418967fa.accept_20_4_9_2_1_213 104 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 149 282 (accept_3_4 103 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 149 282 (Polychromatic418967fa.accept_14_4_9_2_1_95 102 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 149 282 (Polychromatic418967fa.accept_9_2_5_3_1_37 101 149 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 149 282 (accept_3_4 100 149 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 149 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 149 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 149 282
  (Polychromatic418967fa.accept_9_8_5_3_1_777 98 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 149 282 (accept_3_4 97 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 149 282 (Polychromatic418967fa.accept_9_6_5_3_1_205 96 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 149 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 95 149 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 149 282 (accept_3_4 94 149 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 149 282 (Polychromatic418967fa.accept_13_2_6_9_1_2636 93 149 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 149 282
  (Polychromatic418967fa.accept_9_2_5_3_1_37 92 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 149 282 (accept_3_4 91 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 149 282 (Polychromatic418967fa.accept_17_5_13_10_1_3949 90 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 149 282 (Polychromatic418967fa.accept_9_8_5_3_1_777 89 149 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 149 282 (accept_3_4 88 149 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 149 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 149 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 149 282
  (Polychromatic418967fa.accept_15_11_14_12_1_2458 86 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 149 282 (accept_3_4 85 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 149 282 (Polychromatic418967fa.accept_15_9_14_12_1_913 84 149 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 149 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 149 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 149 282 (accept_3_4 82 149 282
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 149 282 (Polychromatic418967fa.accept_10_1_9_2_1_45
  81 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 149 282
  (Polychromatic418967fa.accept_9_8_5_3_1_777 80 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 149 282 (accept_3_4 79 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 149 282 (Polychromatic418967fa.accept_9_6_5_3_1_205 78 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 149 282 (Polychromatic418967fa.accept_10_7_9_2_1_1887 77 149 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 149 282 (accept_3_4 76 149 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 149 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 149 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 149 282
  (Polychromatic418967fa.accept_9_2_5_3_1_37 74 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 149 282 (accept_3_4 73 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 149 282 (Polychromatic418967fa.accept_13_7_6_9_1_1831 72 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 149 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 149 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 149 282 (accept_3_4 70 149 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 149 282 (Polychromatic418967fa.accept_9_6_5_3_1_205 69 149 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 149 282
  (Polychromatic418967fa.accept_13_3_6_9_1_1150 68 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 149 282 (accept_3_4 67 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 149 282 (Polychromatic418967fa.accept_13_1_6_9_1_1197 66 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 149 282 (Polychromatic418967fa.accept_9_2_5_3_1_37 65 149 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 149 282 (accept_3_4 64 149 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 149 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 149 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 149 282
  (Polychromatic418967fa.accept_9_8_5_3_1_777 62 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 149 282 (accept_3_4 61 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 149 282 (Polychromatic418967fa.accept_9_6_5_3_1_205 60 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 149 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 149 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 149 282 (accept_3_4 58 149 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 149 282 (Polychromatic418967fa.accept_10_7_9_2_1_1887 57 149 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 149 282
  (Polychromatic418967fa.accept_9_2_5_3_1_37 56 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 149 282 (accept_3_4 55 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 149 282 (Polychromatic418967fa.accept_13_2_6_9_1_2636 54 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 149 282 (Polychromatic418967fa.accept_9_8_5_3_1_777 53 149 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 149 282 (accept_3_4 52 149 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 149 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 149 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 149 282
  (Polychromatic418967fa.accept_31_19_25_3_1_17310 50 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 149 282 (accept_3_4 49 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 149 282 (Polychromatic418967fa.accept_17_14_13_10_1_3936 48 149 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 149 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 149 282 (accept_3_4 46
  149 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 149 282
  (Polychromatic418967fa.accept_11_1_6_7_1_116 45 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 149 282 (Polychromatic418967fa.accept_9_8_5_3_1_777 44 149 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 149 282 (accept_3_4 43 149 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 149 282 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 149 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 149 282 (Polychromatic418967fa.accept_10_1_9_2_1_45
  41 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 149 282 (accept_3_4 40
  149 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 149 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 149 282 (Polychromatic418967fa.accept_9_2_5_3_1_37 38 149 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 149 282 (accept_3_4 37 149 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 149 282 (Polychromatic418967fa.accept_13_10_6_9_1_1152 36 149 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 149 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 149 282 (accept_3_4 34 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 149 282 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 149 282 (Polychromatic418967fa.accept_14_4_9_2_1_95 32 149 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 149 282 (accept_3_4 31 149 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 149 282 (Polychromatic418967fa.accept_13_4_6_9_1_3401 30 149 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 149 282
  (Polychromatic418967fa.accept_9_2_5_3_1_37 29 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 149 282 (accept_3_4 28 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 149 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 149 282 (Polychromatic418967fa.accept_9_8_5_3_1_777 26 149 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 149 282 (accept_3_4 25 149 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 149 282 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 149 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 149 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 149 282 (accept_3_4 22 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 149 282 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 149 282 (Polychromatic418967fa.accept_9_2_5_3_1_37 20 149 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 149 282 (accept_3_4 19 149 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 149 282 (Polychromatic418967fa.accept_14_4_9_2_1_95 18 149 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 149 282
  (Polychromatic418967fa.accept_9_8_5_3_1_777 17 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 149 282 (accept_3_4 16 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 149 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 149 282 (Polychromatic418967fa.accept_13_1_6_9_1_1197 14 149 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 149 282 (accept_3_4 13 149 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 149 282 (Polychromatic418967fa.accept_11_1_6_7_1_116 12 149
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 149 282 (accept_3_4 10 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  149 282 (Polychromatic418967fa.accept_15_9_14_12_1_913 9 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 149 282 (Polychromatic418967fa.accept_9_8_5_3_1_777 8 149 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 149 282 (accept_3_4 7 149 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 149 282 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 149 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 149 282
  (Polychromatic418967fa.accept_17_5_13_10_1_3949 5 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 149 282 (accept_3_4 4 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  149 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 149 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 149 282 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 149 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 282 (accept_3_4 1 149 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 149
  282))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 135 148 282 (Eq.refl Bool.true) (allA_succ_of_gcd 134 148 282 2 67 74 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 133 148 282
  (Polychromatic418967fa.accept_9_7_4_3_1_204 133 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 132 148 282 2 66 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 131 148 282 (accept_3_5 131 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 130 148 282 2 65 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 129 148 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 129 148 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 128 148 282 2 64 74 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 148 282
  (Polychromatic418967fa.accept_9_1_4_3_1_201 127 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 148 282 2 63 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 148 282 (accept_3_5 125 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 148 282 2 62 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 148 282 (Polychromatic418967fa.accept_9_6_4_3_1_203 123 148 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 148 282 2 61 74 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 148 282
  (Polychromatic418967fa.accept_13_4_5_9_1_1829 121 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 148 282 2 60 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 148 282 (accept_3_5 119 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 148 282 2 59 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 148 282 (Polychromatic418967fa.accept_12_9_4_6_1_460 117 148 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 148 282 2 58 74 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 148 282
  (Polychromatic418967fa.accept_7_3_1_2_1_247 115 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 148 282 2 57 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 148 282 (accept_3_5 113 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 148 282 2 56 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 148 282 (Polychromatic418967fa.accept_7_6_1_2_1_230 111 148 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 148 282 2 55 74 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 148 282
  (Polychromatic418967fa.accept_9_1_4_3_1_201 109 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 148 282 2 54 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 148 282 (accept_3_5 107 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 148 282 2 53 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 148 282 (Polychromatic418967fa.accept_9_6_4_3_1_203 105 148 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 148 282 2 52 74 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 148 282
  (Polychromatic418967fa.accept_19_8_15_16_1_5109 103 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 148 282 2 51 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 148 282 (accept_3_5 101 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 148 282 2 50 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 148 282 (Polychromatic418967fa.accept_12_3_4_6_1_434 99 148 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 148 282 2 49 74 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 148 282
  (Polychromatic418967fa.accept_7_6_1_2_1_230 97 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 148 282 2 48 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 148 282 (accept_3_5 95 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 148 282 2 47 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 148 282 (Polychromatic418967fa.accept_12_9_4_6_1_460 93 148 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 148 282 2 46 74 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 148 282
  (Polychromatic418967fa.accept_9_1_4_3_1_201 91 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 148 282 2 45 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 148 282 (accept_3_5 89 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 148 282 2 44 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 148 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 87 148 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 148 282 2 43 74 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 148 282
  (Polychromatic418967fa.accept_10_5_8_2_1_517 85 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 148 282 2 42 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 148 282 (accept_3_5 83 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 148 282 2 41 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 148 282 (Polychromatic418967fa.accept_12_9_4_6_1_460 81 148 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 148 282 2 40 74 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 148 282
  (Polychromatic418967fa.accept_9_7_4_3_1_204 79 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 148 282 2 39 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 148 282 (accept_3_5 77 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 148 282 2 38 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 148 282 (Polychromatic418967fa.accept_10_5_8_2_1_517 75 148 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 148 282 2 37 74 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 148 282
  (Polychromatic418967fa.accept_7_3_1_2_1_247 73 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 148 282 2 36 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 148 282 (accept_3_5 71 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 148 282 2 35 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 148 282 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 148 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 148 282 2 34 74 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 148 282
  (Polychromatic418967fa.accept_13_2_5_9_1_610 67 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 148 282 2 33 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 148 282 (accept_3_5 65 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 148 282 2 32 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 148 282 (Polychromatic418967fa.accept_12_3_4_6_1_434 63 148 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 148 282 2 31 74 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 148 282
  (Polychromatic418967fa.accept_9_7_4_3_1_204 61 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 148 282 2 30 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 148 282 (accept_3_5 59 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 148 282 2 29 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 148 282 (Polychromatic418967fa.accept_12_9_4_6_1_460 57 148 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 148 282 2 28 74 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 148 282
  (Polychromatic418967fa.accept_7_6_1_2_1_230 55 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 148 282 2 27 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 148 282 (accept_3_5 53 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 148 282 2 26 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 148 282 (Polychromatic418967fa.accept_9_6_4_3_1_203 51 148 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 148 282 2 25 74 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 148 282
  (Polychromatic418967fa.accept_19_11_15_16_1_9396 49 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 148 282 2 24 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 148 282 (accept_3_5 47 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 148 282 2 23 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 148 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 148 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 148 282 2 22 74 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 148 282
  (Polychromatic418967fa.accept_9_7_4_3_1_204 43 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 148 282 2 21 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 148 282 (accept_3_5 41 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 148 282 2 20 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 148 282 (Polychromatic418967fa.accept_12_3_4_6_1_434 39 148 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 148 282 2 19 74 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 148 282
  (Polychromatic418967fa.accept_9_1_4_3_1_201 37 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 148 282 2 18 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 148 282 (accept_3_5 35 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 148 282 2 17 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 148 282 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 148 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 148 282 2 16 74 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 148 282
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 148 282 2 15 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 148 282 (accept_3_5 29 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 148 282 2 14 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 148 282 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 148 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 148 282 2 13 74 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 148 282
  (Polychromatic418967fa.accept_9_7_4_3_1_204 25 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 148 282 2 12 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 148 282 (accept_3_5 23 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 148 282 2 11 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 148 282 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 148 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 148 282 2 10 74 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 148 282
  (Polychromatic418967fa.accept_9_1_4_3_1_201 19 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 148 282 2 9 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 148 282 (accept_3_5 17 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 148 282 2 8 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 148 282 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 148 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 148 282 2 7 74 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 148 282
  (Polychromatic418967fa.accept_7_6_1_2_1_230 13 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 148 282 2 6 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 148 282 (accept_3_5 11 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 148 282 2 5 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 148 282 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 148 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 148 282 2 4 74 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 148 282
  (Polychromatic418967fa.accept_9_7_4_3_1_204 7 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 148 282 2 3 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 148 282 (accept_3_5 5 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 148
  282 2 2 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  148 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 148 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 148 282 2 1 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 148 282 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 148 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148
  282)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 136 147 282 (Eq.refl Bool.true) (allA_succ_of_gcd 135 147 282 3 45 49 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 134 147 282
  (Polychromatic418967fa.accept_10_4_7_2_1_211 134 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 133 147 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 133 147 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 132 147 282 3 44 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 131 147 282 (Polychromatic418967fa.accept_14_5_7_2_1_468
  131 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 147 282
  (Polychromatic418967fa.accept_12_10_3_6_1_882 130 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 129 147 282 3 43 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 128 147 282 (Polychromatic418967fa.accept_12_8_3_6_1_909 128 147 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 147 282
  (Polychromatic418967fa.accept_18_1_3_12_1_467 127 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 147 282 3 42 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 147 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 125 147 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 147 282 (Polychromatic418967fa.accept_10_4_7_2_1_211
  124 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 123 147 282 3 41 49 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 122 147 282
  (Polychromatic418967fa.accept_12_2_3_6_1_112 122 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 147 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 121 147 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 147 282 3 40 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 147 282 (Polychromatic418967fa.accept_10_9_7_2_1_887
  119 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 147 282
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 118 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 117 147 282 3 39 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 116 147 282 (Polychromatic418967fa.accept_12_8_3_6_1_909 116 147 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 147 282
  (Polychromatic418967fa.accept_10_5_7_2_1_516 115 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 147 282 3 38 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 147 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 113 147 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 147 282 (Polychromatic418967fa.accept_12_4_3_6_1_879
  112 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 111 147 282 3 37 49 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 110 147 282
  (Polychromatic418967fa.accept_12_2_3_6_1_112 110 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 147 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 109 147 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 147 282 3 36 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 147 282 (Polychromatic418967fa.accept_11_8_4_7_1_1303
  107 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 147 282
  (Polychromatic418967fa.accept_12_10_3_6_1_882 106 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 147 282 3 35 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 147 282 (Polychromatic418967fa.accept_10_4_7_2_1_211 104 147 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 147 282
  (Polychromatic418967fa.accept_14_5_7_2_1_468 103 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 147 282 3 34 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 147 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 101 147 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 147 282 (Polychromatic418967fa.accept_12_4_3_6_1_879
  100 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 147 282 3 33 49 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 147 282
  (Polychromatic418967fa.accept_12_2_3_6_1_112 98 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 147 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 147 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 147 282 3 32 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 147 282 (Polychromatic418967fa.accept_10_5_7_2_1_516
  95 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 147 282
  (Polychromatic418967fa.accept_10_4_7_2_1_211 94 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 147 282 3 31 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 147 282 (Polychromatic418967fa.accept_12_8_3_6_1_909 92 147 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 147 282 (Polychromatic418967fa.accept_11_3_4_7_1_114
  91 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 147 282 3 30 49 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 147 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 147 282 (Polychromatic418967fa.accept_12_4_3_6_1_879 88 147 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 147 282 3 29 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 147 282 (Polychromatic418967fa.accept_12_2_3_6_1_112
  86 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 147 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 85 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 147 282 3 28 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 147 282 (Polychromatic418967fa.accept_13_5_4_9_1_601 83 147 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 147 282 (Polychromatic418967fa.accept_12_10_3_6_1_882
  82 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 147 282 3 27 49 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 147 282
  (Polychromatic418967fa.accept_11_3_4_7_1_114 80 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 147 282 (Polychromatic418967fa.accept_10_9_7_2_1_887 79 147 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 147 282 3 26 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 147 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 77
  147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 147 282
  (Polychromatic418967fa.accept_12_4_3_6_1_879 76 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 147 282 3 25 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 147 282 (Polychromatic418967fa.accept_10_4_7_2_1_211 74 147 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 147 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 73
  147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 147 282 3 24 49 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 147 282
  (Polychromatic418967fa.accept_13_6_4_9_1_4326 71 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 147 282 (Polychromatic418967fa.accept_12_10_3_6_1_882 70 147 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 147 282 3 23 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 147 282 (Polychromatic418967fa.accept_12_8_3_6_1_909
  68 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 147 282
  (Polychromatic418967fa.accept_18_13_3_12_1_3207 67 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 147 282 3 22 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 147 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 147 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 147 282
  (Polychromatic418967fa.accept_10_4_7_2_1_211 64 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 147 282 3 21 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 147 282 (Polychromatic418967fa.accept_12_2_3_6_1_112 62 147 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 147 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 61
  147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 147 282 3 20 49 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 147 282
  (Polychromatic418967fa.accept_10_9_7_2_1_887 59 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 147 282 (Polychromatic418967fa.accept_11_3_4_7_1_114 58 147 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 147 282 3 19 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 147 282 (Polychromatic418967fa.accept_12_8_3_6_1_909
  56 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 147 282
  (Polychromatic418967fa.accept_10_5_7_2_1_516 55 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 147 282 3 18 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 147 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 147 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 147 282 (Polychromatic418967fa.accept_11_8_4_7_1_1303
  52 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 147 282 3 17 49 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 147 282
  (Polychromatic418967fa.accept_12_2_3_6_1_112 50 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 147 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 147 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 147 282 3 16 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 147 282 (Polychromatic418967fa.accept_11_3_4_7_1_114
  47 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 147 282
  (Polychromatic418967fa.accept_12_10_3_6_1_882 46 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 147 282 3 15 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 147 282 (Polychromatic418967fa.accept_10_4_7_2_1_211 44 147 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 282
  (Polychromatic418967fa.accept_18_7_3_12_1_3241 43 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 147 282 3 14 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 147 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 147 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 282 (Polychromatic418967fa.accept_12_4_3_6_1_879
  40 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 147 282 3 13 49 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 147 282
  (Polychromatic418967fa.accept_12_2_3_6_1_112 38 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 147 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 147 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 147 282 3 12 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 147 282 (Polychromatic418967fa.accept_10_5_7_2_1_516
  35 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 282
  (Polychromatic418967fa.accept_10_4_7_2_1_211 34 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 147 282 3 11 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 147 282 (Polychromatic418967fa.accept_12_8_3_6_1_909 32 147 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 282 (Polychromatic418967fa.accept_13_5_4_9_1_601
  31 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 147 282 3 10 49 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 147 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 147 282 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 147 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 147 282 3 9 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 147 282 (Polychromatic418967fa.accept_12_2_3_6_1_112
  26 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 147 282 3 8 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 147 282 (Polychromatic418967fa.accept_14_9_7_2_1_2483 23 147 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 282 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 147
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 147 282 3 7 49 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 147 282
  (Polychromatic418967fa.accept_12_8_3_6_1_909 20 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 147 282 (Polychromatic418967fa.accept_10_9_7_2_1_887 19 147 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 147 282 3 6 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 147 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 282
  (Polychromatic418967fa.accept_12_4_3_6_1_879 16 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 147 282 3 5 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 147 282 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 147 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 147 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 147 282 3 4 49 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 147 282
  (Polychromatic418967fa.accept_19_11_14_16_1_9370 11 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 147 282 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 147 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 147 282 3 3 49 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 147 282
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 8 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 147 282 (Polychromatic418967fa.accept_13_7_4_9_1_1865 7 147 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 147 282 3 2 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 147 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 147 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 282
  (Polychromatic418967fa.accept_10_4_7_2_1_211 4 147 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 147 282 3 1 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 147 282 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 147 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 147 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147
  282))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 137 146 282 (Eq.refl Bool.true) (allA_succ_of_gcd 136 146 282 2 68 73 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 135 146 282
  (Polychromatic418967fa.accept_12_3_2_6_1_138 135 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 134 146 282 2 67 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 133 146 282 (accept_3_4 133 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 132 146 282 2 66 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 131 146 282 (Polychromatic418967fa.accept_9_5_2_3_1_194 131 146 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 130 146 282 2 65 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 129 146 282
  (Polychromatic418967fa.accept_7_3_6_2_1_90 129 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 128 146 282 2 64 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 127 146 282 (accept_3_4 127 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 146 282 2 63 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 146 282 (Polychromatic418967fa.accept_9_8_2_3_1_447 125 146 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 146 282 2 62 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 146 282
  (Polychromatic418967fa.accept_7_4_6_2_1_451 123 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 146 282 2 61 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 146 282 (accept_3_4 121 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 146 282 2 60 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 146 282 (Polychromatic418967fa.accept_13_2_3_9_1_2610 119 146 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 146 282 2 59 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 146 282
  (Polychromatic418967fa.accept_12_9_2_6_1_455 117 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 146 282 2 58 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 146 282 (accept_3_4 115 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 146 282 2 57 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 146 282 (Polychromatic418967fa.accept_7_1_6_2_1_18 113 146 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 146 282 2 56 73 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 146 282
  (Polychromatic418967fa.accept_10_1_6_2_1_867 111 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 146 282 2 55 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 146 282 (accept_3_4 109 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 146 282 2 54 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 146 282 (Polychromatic418967fa.accept_9_8_2_3_1_447 107 146 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 146 282 2 53 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 146 282
  (Polychromatic418967fa.accept_9_6_2_3_1_771 105 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 146 282 2 52 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 146 282 (accept_3_4 103 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 146 282 2 51 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 146 282 (Polychromatic418967fa.accept_7_3_6_2_1_90 101 146 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 146 282 2 50 73 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 146 282
  (Polychromatic418967fa.accept_7_1_6_2_1_18 99 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 146 282 2 49 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 146 282 (accept_3_4 97 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 146 282 2 48 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 146 282 (Polychromatic418967fa.accept_7_4_6_2_1_451 95 146 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 146 282 2 47 73 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 146 282
  (Polychromatic418967fa.accept_12_9_2_6_1_455 93 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 146 282 2 46 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 146 282 (accept_3_4 91 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 146 282 2 45 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 146 282 (Polychromatic418967fa.accept_9_8_2_3_1_447 89 146 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 146 282 2 44 73 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 146 282
  (Polychromatic418967fa.accept_7_3_6_2_1_90 87 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 146 282 2 43 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 146 282 (accept_3_4 85 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 146 282 2 42 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 146 282 (Polychromatic418967fa.accept_13_5_3_9_1_1189 83 146 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 146 282 2 41 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 146 282
  (Polychromatic418967fa.accept_7_4_6_2_1_451 81 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 146 282 2 40 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 146 282 (accept_3_4 79 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 146 282 2 39 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 146 282 (Polychromatic418967fa.accept_9_5_2_3_1_194 77 146 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 146 282 2 38 73 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 146 282
  (Polychromatic418967fa.accept_12_3_2_6_1_138 75 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 146 282 2 37 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 146 282 (accept_3_4 73 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 146 282 2 36 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 146 282 (Polychromatic418967fa.accept_7_1_6_2_1_18 71 146 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 146 282 2 35 73 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 146 282
  (Polychromatic418967fa.accept_9_6_2_3_1_771 69 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 146 282 2 34 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 146 282 (accept_3_4 67 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 146 282 2 33 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 146 282 (Polychromatic418967fa.accept_11_10_3_7_1_2564 65 146 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 146 282 2 32 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 146 282
  (Polychromatic418967fa.accept_12_3_2_6_1_138 63 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 146 282 2 31 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 146 282 (accept_3_4 61 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 146 282 2 30 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 146 282 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 146 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 146 282 2 29 73 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 146 282
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 146 282 2 28 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 146 282 (accept_3_4 55 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 146 282 2 27 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 146 282 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 146 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 146 282 2 26 73 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 146 282
  (Polychromatic418967fa.accept_9_6_2_3_1_771 51 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 146 282 2 25 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 146 282 (accept_3_4 49 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 146 282 2 24 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 146 282 (Polychromatic418967fa.accept_13_8_3_9_1_5269 47 146 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 146 282 2 23 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 146 282
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 146 282 2 22 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 146 282 (accept_3_4 43 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 146 282 2 21 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 146 282 (Polychromatic418967fa.accept_9_5_2_3_1_194 41 146 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 146 282 2 20 73 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 146 282
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 146 282 2 19 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 146 282 (accept_3_4 37 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 146 282 2 18 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 146 282 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 146 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 146 282 2 17 73 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 146 282
  (Polychromatic418967fa.accept_9_6_2_3_1_771 33 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 146 282 2 16 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 146 282 (accept_3_4 31 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 146 282 2 15 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 146 282 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 146 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 146 282 2 14 73 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 146 282
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 146 282 2 13 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 146 282 (accept_3_4 25 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 146 282 2 12 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 146 282 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 146 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 146 282 2 11 73 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 146 282
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 146 282 2 10 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 146 282 (accept_3_4 19 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 146 282 2 9 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 146 282 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 146 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 282 2 8 73 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 282
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 146 282 2 7 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 146 282 (accept_3_4 13 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 146 282 2 6 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 146 282 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 146 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 146 282 2 5 73 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 146 282
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 146 282 2 4 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 146 282 (accept_3_4 7 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 146
  282 2 3 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  146 282 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 146 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 146 282 2 2 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 146 282 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 146 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 146 282 2 1 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 146 282 (accept_3_4 1 146 282
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  282)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 138 145 282 (Eq.refl Bool.true) (allA_succ_of_accept 137 145 282 (accept_3_5 137 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 136 145 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 136 145
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 135 145 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 135 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 134 145 282 (accept_3_5 134 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  133 145 282 (Polychromatic418967fa.accept_9_7_1_3_1_443 133 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 132 145 282 (Polychromatic418967fa.accept_9_6_1_3_1_191 132 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 145 282 (accept_3_5 131 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 145 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 130 145
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 145 282
  (Polychromatic418967fa.accept_7_3_5_2_1_17 129 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 128 145 282 (accept_3_5 128 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  127 145 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 127 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 126 145 282 (Polychromatic418967fa.accept_15_6_10_12_1_2538 126 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 145 282 (accept_3_5 125 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 145 282 (Polychromatic418967fa.accept_9_7_1_3_1_443 124 145
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 145 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 123 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 145 282 (accept_3_5 122 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 145 282 (Polychromatic418967fa.accept_9_4_1_3_1_190 121 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 145 282 (Polychromatic418967fa.accept_13_3_2_9_1_1187 120 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 145 282 (accept_3_5 119 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 145 282 (Polychromatic418967fa.accept_10_8_5_2_1_881 118 145
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 145 282
  (Polychromatic418967fa.accept_10_7_5_2_1_880 117 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 145 282 (accept_3_5 116 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 145 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 115 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 145 282 (Polychromatic418967fa.accept_9_6_1_3_1_191 114 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 145 282 (accept_3_5 113 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 145 282 (Polychromatic418967fa.accept_9_4_1_3_1_190 112 145
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 145 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 111 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 145 282 (accept_3_5 110 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 145 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 109 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 145 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 108 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 145 282 (accept_3_5 107 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 145 282 (Polychromatic418967fa.accept_9_7_1_3_1_443 106 145
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 145 282
  (Polychromatic418967fa.accept_9_6_1_3_1_191 105 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 145 282 (accept_3_5 104 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 145 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 103 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 145 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 102 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 145 282 (accept_3_5 101 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 145 282 (Polychromatic418967fa.accept_19_5_12_16_1_9303 100
  145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 145 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 99 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 145 282 (accept_3_5 98 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 145 282 (Polychromatic418967fa.accept_9_7_1_3_1_443 97 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 145 282 (Polychromatic418967fa.accept_9_6_1_3_1_191 96 145 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 145 282 (accept_3_5 95 145 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 145 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 94 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 145 282
  (Polychromatic418967fa.accept_10_3_5_2_1_38 93 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 145 282 (accept_3_5 92 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 145 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 145 282 (Polychromatic418967fa.accept_19_14_12_16_1_7952 90 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 145 282 (accept_3_5 89 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 145 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 88 145 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 145 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 87 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 145 282 (accept_3_5 86 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 145 282 (Polychromatic418967fa.accept_9_4_1_3_1_190 85 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 145 282 (Polychromatic418967fa.accept_13_6_2_9_1_1188 84 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 145 282 (accept_3_5 83 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 145 282 (Polychromatic418967fa.accept_15_7_10_12_1_2403 82 145
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 145 282
  (Polychromatic418967fa.accept_7_4_5_2_1_243 81 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 145 282 (accept_3_5 80 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 145 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 145 282 (Polychromatic418967fa.accept_9_6_1_3_1_191 78 145 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 145 282 (accept_3_5 77 145 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 145 282 (Polychromatic418967fa.accept_9_4_1_3_1_190 76 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 145 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 145 282 (accept_3_5 74 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 145 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 73 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 145 282 (Polychromatic418967fa.accept_13_7_2_9_1_1826 72 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 145 282 (accept_3_5 71 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 145 282 (Polychromatic418967fa.accept_9_7_1_3_1_443 70 145 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 145 282
  (Polychromatic418967fa.accept_9_6_1_3_1_191 69 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 145 282 (accept_3_5 68 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 145 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 145 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 145 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 145 282 (accept_3_5 65 145 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 145 282 (Polychromatic418967fa.accept_11_9_2_7_1_1298 64 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 145 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 145 282 (accept_3_5 62 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 145 282 (Polychromatic418967fa.accept_9_7_1_3_1_443 61 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 145 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 145 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 145 282 (accept_3_5 59 145 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 145 282 (Polychromatic418967fa.accept_9_4_1_3_1_190 58 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 145 282
  (Polychromatic418967fa.accept_10_7_5_2_1_880 57 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 145 282 (accept_3_5 56 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 145 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 145 282 (Polychromatic418967fa.accept_15_9_10_12_1_1625 54 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 145 282 (accept_3_5 53 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 145 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 145 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 145 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 145 282 (accept_3_5 50 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 145 282 (Polychromatic418967fa.accept_9_4_1_3_1_190 49 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 145 282 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 145 282 (accept_3_5 47 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 145 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 145 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 145 282
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 145 282 (accept_3_5 44 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 145 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 145 282 (Polychromatic418967fa.accept_9_6_1_3_1_191 42 145 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 145 282 (accept_3_5 41 145 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 145 282 (Polychromatic418967fa.accept_9_4_1_3_1_190 40 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 145 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 145 282 (accept_3_5 38 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 145 282 (Polychromatic418967fa.accept_10_7_5_2_1_880 37 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 145 282 (Polychromatic418967fa.accept_15_6_10_12_1_2538 36 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 145 282 (accept_3_5 35 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 145 282 (Polychromatic418967fa.accept_9_7_1_3_1_443 34 145 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 145 282
  (Polychromatic418967fa.accept_9_6_1_3_1_191 33 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 145 282 (accept_3_5 32 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 145 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 145 282 (Polychromatic418967fa.accept_17_13_9_10_1_2888 30 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 145 282 (accept_3_5 29 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 145 282 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 145
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 145 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 145 282 (accept_3_5 26 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 145 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 145 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 145 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 145 282 (accept_3_5 23 145 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 145 282 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 282
  (Polychromatic418967fa.accept_14_7_5_2_1_2473 21 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 145 282 (accept_3_5 20 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 145 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 145 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 145 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 282 (accept_3_5 17 145 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 145 282 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 145 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 145 282 (accept_3_5 14 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 145 282 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 145 282 (Polychromatic418967fa.accept_21_12_19_9_1_8442 12 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 282 (accept_3_5 11 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 145 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 145 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 145 282
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 145 282 (accept_3_5 8 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  145 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 145 282 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 145 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 145 282 (accept_3_5 5 145 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 145 282 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 145 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 145 282
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 145 282 (accept_3_5 2 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  145 282 (Polychromatic418967fa.accept_13_1_2_9_1_1186 1 145 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 145
  282))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 139 144 282 (Eq.refl Bool.true) (allA_succ_of_gcd 138 144 282 6 23 24 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 137 144 282
  (Polychromatic418967fa.accept_10_7_4_2_1_903 137 144 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 136 144 282 2 68 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 135 144 282 3 45 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 134 144 282 2 67 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 133 144 282 (Polychromatic418967fa.accept_21_7_18_9_1_5291 133 144
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 132 144 282 6 22 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 131 144 282
  (Polychromatic418967fa.accept_7_5_4_2_1_235 131 144 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 130 144 282 2 65 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 129 144 282 3 43 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 128 144 282 2 64 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 144 282 (Polychromatic418967fa.accept_10_7_4_2_1_903 127 144
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 144 282 6 21 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 144 282
  (Polychromatic418967fa.accept_7_6_4_2_1_236 125 144 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 144 282 2 62 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 123 144 282 3 41 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 122 144 282 2 61 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 144 282 (Polychromatic418967fa.accept_14_9_4_2_1_983 121 144
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 144 282 6 20 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 144 282
  (Polychromatic418967fa.accept_13_2_1_9_1_1174 119 144 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 144 282 2 59 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 117 144 282 3 39 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 116 144 282 2 58 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 144 282 (Polychromatic418967fa.accept_13_11_1_9_1_1179 115 144
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 144 282 6 19 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 144 282
  (Polychromatic418967fa.accept_21_8_18_9_1_5329 113 144 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 112 144 282 2 56 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 111 144 282 3 37 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 110 144 282 2 55 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 144 282 (Polychromatic418967fa.accept_13_5_1_9_1_618
  109 144 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 144 282 6 18 24 47
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 144 282
  (Polychromatic418967fa.accept_10_7_4_2_1_903 107 144 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 144 282 2 53 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 105 144 282 3 35 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 104 144 282 2 52 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 144 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 103 144
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 144 282 6 17 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 144 282
  (Polychromatic418967fa.accept_13_10_1_9_1_3380 101 144 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 144 282 2 50 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 99 144 282 3 33 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 144 282 2 49 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 144 282 (Polychromatic418967fa.accept_7_6_4_2_1_236 97
  144 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 144 282 6 16 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 144 282
  (Polychromatic418967fa.accept_15_5_9_12_1_1599 95 144 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 144 282 2 47 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 93 144 282 3 31 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 92 144 282 2 46 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 144 282 (Polychromatic418967fa.accept_19_15_11_16_1_6492 91 144
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 144 282 6 15 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 144 282
  (Polychromatic418967fa.accept_7_5_4_2_1_235 89 144 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 144 282 2 44 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 87 144 282 3 29 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 86 144 282 2 43 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 144 282 (Polychromatic418967fa.accept_15_10_9_12_1_2497 85 144
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 144 282 6 14 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 144 282
  (Polychromatic418967fa.accept_7_6_4_2_1_236 83 144 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 144 282 2 41 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 144 282 3 27 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 80 144 282 2 40 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 144 282 (Polychromatic418967fa.accept_14_9_4_2_1_983 79 144 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 144 282 6 13 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 144 282
  (Polychromatic418967fa.accept_10_7_4_2_1_903 77 144 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 144 282 2 38 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 144 282 3 25 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 144 282 2 37 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 144 282 (Polychromatic418967fa.accept_13_8_1_9_1_1178 73 144
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 144 282 6 12 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 144 282
  (Polychromatic418967fa.accept_13_6_1_9_1_619 71 144 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 144 282 2 35 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 144 282 3 23 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 144 282 2 34 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 144 282 (Polychromatic418967fa.accept_10_7_4_2_1_903 67 144 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 144 282 6 11 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 144 282
  (Polychromatic418967fa.accept_14_9_4_2_1_983 65 144 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 144 282 2 32 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 144 282 3 21 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 62 144 282 2 31 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 144 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 61 144 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 144 282 6 10 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 144 282
  (Polychromatic418967fa.accept_15_14_9_12_1_2498 59 144 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 144 282 2 29 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 57 144 282 3 19 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 144 282 2 28 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 144 282 (Polychromatic418967fa.accept_7_6_4_2_1_236 55
  144 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 144 282 6 9 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 144 282
  (Polychromatic418967fa.accept_17_2_8_10_1_2870 53 144 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 144 282 2 26 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 144 282 3 17 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 144 282 2 25 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 144 282 (Polychromatic418967fa.accept_13_10_1_9_1_3380 49 144
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 144 282 6 8 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 144 282
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 144 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 144 282 2 23 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 144 282 3 15 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 144 282 2 22 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 144 282 (Polychromatic418967fa.accept_19_5_11_16_1_8010 43 144
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 144 282 6 7 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 144 282
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 144 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 144 282 2 20 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 144 282 3 13 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 144 282 2 19 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 144 282 (Polychromatic418967fa.accept_10_7_4_2_1_903 37 144 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 144 282 6 6 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 144 282
  (Polychromatic418967fa.accept_15_5_9_12_1_1599 35 144 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 144 282 2 17 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 144 282 3 11 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 144 282 2 16 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 144 282 (Polychromatic418967fa.accept_13_5_1_9_1_618 31 144 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 144 282 6 5 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 144 282
  (Polychromatic418967fa.accept_15_14_9_12_1_2498 29 144 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 144 282 2 14 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 27 144 282 3 9 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 26 144 282 2 13 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 144 282 (Polychromatic418967fa.accept_15_10_9_12_1_2497 25 144
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 144 282 6 4 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 144 282
  (Polychromatic418967fa.accept_13_10_1_9_1_3380 23 144 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 144 282 2 11 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 144 282 3 7 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 144 282 2 10 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 144 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 144 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 144 282 6 3 24 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 144 282
  (Polychromatic418967fa.accept_10_7_4_2_1_903 17 144 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 144 282 2 8 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 144 282 3 5 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 144 282 2 7 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 144 282 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 144 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 282 6 2 24 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 282
  (Polychromatic418967fa.accept_13_11_1_9_1_1179 11 144 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 144 282 2 5 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 144 282 3 3 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 144 282 2 4 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 144 282 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 144 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 282 6 1 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 282 (Polychromatic418967fa.accept_7_5_4_2_1_235 5
  144 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 282 2 2 72 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 144 282 3 1 48 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 144 282 2 1 72 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 282
  (Polychromatic418967fa.accept_21_1_18_9_1_5290 1 144 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 144
  282)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 140 143 282 (Eq.refl Bool.true) (allA_succ_of_accept 139 143 282 (accept_3_4 139 143 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 138 143 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 138 143
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 137 143 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 137 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 136 143 282 (accept_3_4 136 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  135 143 282 (Polychromatic418967fa.accept_10_5_3_2_1_899 135 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 134 143 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 134 143 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 143 282 (accept_3_4 133 143 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 143 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 132 143
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 143 282
  (Polychromatic418967fa.accept_7_5_3_2_1_249 131 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 130 143 282 (accept_3_4 130 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  129 143 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 129 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 128 143 282 (Polychromatic418967fa.accept_9_2_8_3_1_181 128 143 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 143 282 (accept_3_4 127 143 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 143 282 (Polychromatic418967fa.accept_16_14_15_10_1_5910 126
  143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 143 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 125 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 143 282 (accept_3_4 124 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 143 282 (Polychromatic418967fa.accept_9_6_8_3_1_183 123 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 143 282 (Polychromatic418967fa.accept_9_5_8_3_1_437 122 143 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 143 282 (accept_3_4 121 143 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 143 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 120 143
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 143 282
  (Polychromatic418967fa.accept_9_2_8_3_1_181 119 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 143 282 (accept_3_4 118 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 143 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 117 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 143 282 (Polychromatic418967fa.accept_15_11_8_12_1_4437 116 143 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 143 282 (accept_3_4 115 143 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 143 282 (Polychromatic418967fa.accept_9_6_8_3_1_183 114 143
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 143 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 113 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 143 282 (accept_3_4 112 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 143 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 111 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 143 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 110 143 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 143 282 (accept_3_4 109 143 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 143 282 (Polychromatic418967fa.accept_15_3_8_12_1_900 108 143
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 143 282
  (Polychromatic418967fa.accept_16_11_15_10_1_3515 107 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 143 282 (accept_3_4 106 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 143 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 105 143 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 143 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 104 143
  282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 143 282 (accept_3_4 103 143
  282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 143 282
  (Polychromatic418967fa.accept_19_7_10_16_1_9388 102 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 143 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 101 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 143 282 (accept_3_4 100 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 143 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 99 143 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 143 282
  (Polychromatic418967fa.accept_20_18_3_2_1_5929 98 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 143 282 (accept_3_4 97 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 143 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 96 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 143 282 (Polychromatic418967fa.accept_9_5_8_3_1_437 95 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 143 282 (accept_3_4 94 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 143 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 143 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 143 282
  (Polychromatic418967fa.accept_7_1_3_2_1_13 92 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 143 282 (accept_3_4 91 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 143 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 90 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 143 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 89 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 143 282 (accept_3_4 88 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 143 282 (Polychromatic418967fa.accept_9_6_8_3_1_183 87 143 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 143 282
  (Polychromatic418967fa.accept_9_5_8_3_1_437 86 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 143 282 (accept_3_4 85 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 143 282 (Polychromatic418967fa.accept_17_16_7_10_1_5179 84 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 143 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 83 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 143 282 (accept_3_4 82 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 143 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 143 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 143 282
  (Polychromatic418967fa.accept_15_5_8_12_1_2435 80 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 143 282 (accept_3_4 79 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 143 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 143 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 143 282 (accept_3_4 76 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 143 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 143 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 143 282
  (Polychromatic418967fa.accept_9_2_8_3_1_181 74 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 143 282 (accept_3_4 73 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 143 282 (Polychromatic418967fa.accept_22_6_11_18_1_11255 72 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 71 143 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 71 143 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 143 282 (accept_3_4 70 143 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 143 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 143 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 143 282
  (Polychromatic418967fa.accept_7_5_3_2_1_249 68 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 143 282 (accept_3_4 67 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 143 282 (Polychromatic418967fa.accept_19_9_10_16_1_6463 66 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 143 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 143 282 (accept_3_4 64 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 143 282 (Polychromatic418967fa.accept_15_3_8_12_1_900 63 143 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 143 282
  (Polychromatic418967fa.accept_7_6_3_2_1_461 62 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 143 282 (accept_3_4 61 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 143 282 (Polychromatic418967fa.accept_9_6_8_3_1_183 60 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 143 282 (Polychromatic418967fa.accept_9_5_8_3_1_437 59 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 143 282 (accept_3_4 58 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 143 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 143 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 143 282
  (Polychromatic418967fa.accept_9_2_8_3_1_181 56 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 143 282 (accept_3_4 55 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 143 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 143 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 143 282 (accept_3_4 52 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 143 282 (Polychromatic418967fa.accept_9_6_8_3_1_183 51 143 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 143 282
  (Polychromatic418967fa.accept_7_1_3_2_1_13 50 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 143 282 (accept_3_4 49 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 143 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 143 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 143 282 (accept_3_4 46 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 143 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 143 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 143 282
  (Polychromatic418967fa.accept_19_6_10_16_1_7989 44 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 143 282 (accept_3_4 43 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 143 282 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 143 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 143 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 143 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 143 282 (accept_3_4 40 143 282
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 143 282
  (Polychromatic418967fa.accept_19_1_10_16_1_6510 39 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 143 282 (Polychromatic418967fa.accept_9_2_8_3_1_181 38 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 143 282 (accept_3_4 37 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 143 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 143 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 143 282
  (Polychromatic418967fa.accept_10_5_3_2_1_899 35 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 143 282 (accept_3_4 34 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 143 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 143 282 (Polychromatic418967fa.accept_9_5_8_3_1_437 32 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 282 (accept_3_4 31 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 143 282 (Polychromatic418967fa.accept_16_14_15_10_1_5910 30 143 282
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 143 282 (accept_3_4 28 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 143 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 143 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 143 282 (accept_3_4 25 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 282 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 143 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 282
  (Polychromatic418967fa.accept_9_5_8_3_1_437 23 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 143 282 (accept_3_4 22 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 143 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 143 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 282 (accept_3_4 19 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 282 (Polychromatic418967fa.accept_15_3_8_12_1_900 18 143 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 143 282 (accept_3_4 16 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 143 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 143 282 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 143 282 (accept_3_4 13 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 143 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 143 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 282
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 143 282 (accept_3_4 10 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  143 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 143 282 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 282 (accept_3_4 7 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 282 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 143 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 282
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 282 (accept_3_4 4 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 282 (Polychromatic418967fa.accept_15_3_8_12_1_900 3 143 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 282 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 282 (accept_3_4 1 143 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 143
  282))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 141 142 282 (Eq.refl Bool.true) (allA_succ_of_gcd 140 142 282 2 70 71 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 139 142 282
  (Polychromatic418967fa.accept_9_4_7_3_1_43 139 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 138 142 282 2 69 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 137 142 282 (accept_3_5 137 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 136 142 282 2 68 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 135 142 282 (Polychromatic418967fa.accept_11_3_10_7_1_129 135 142 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 134 142 282 2 67 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 133 142 282
  (Polychromatic418967fa.accept_13_3_12_9_1_1193 133 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 132 142 282 2 66 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 131 142 282 (accept_3_5 131 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 130 142 282 2 65 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 129 142 282 (Polychromatic418967fa.accept_12_9_10_6_1_872 129 142 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 128 142 282 2 64 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 142 282
  (Polychromatic418967fa.accept_9_1_7_3_1_41 127 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 142 282 2 63 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 142 282 (accept_3_5 125 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 142 282 2 62 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 142 282 (Polychromatic418967fa.accept_9_6_7_3_1_436 123 142 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 142 282 2 61 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 142 282
  (Polychromatic418967fa.accept_9_4_7_3_1_43 121 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 142 282 2 60 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 142 282 (accept_3_5 119 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 142 282 2 59 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 142 282 (Polychromatic418967fa.accept_12_9_10_6_1_872 117 142 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 142 282 2 58 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 142 282
  (Polychromatic418967fa.accept_15_10_7_12_1_2490 115 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 114 142 282 2 57 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 113 142 282 (accept_3_5 113 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 142 282 2 56 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 142 282 (Polychromatic418967fa.accept_12_3_10_6_1_442 111 142 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 142 282 2 55 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 142 282
  (Polychromatic418967fa.accept_9_1_7_3_1_41 109 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 142 282 2 54 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 142 282 (accept_3_5 107 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 142 282 2 53 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 142 282 (Polychromatic418967fa.accept_9_6_7_3_1_436 105 142 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 142 282 2 52 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 142 282
  (Polychromatic418967fa.accept_9_4_7_3_1_43 103 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 142 282 2 51 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 142 282 (accept_3_5 101 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 142 282 2 50 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 142 282 (Polychromatic418967fa.accept_12_3_10_6_1_442 99 142 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 142 282 2 49 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 142 282
  (Polychromatic418967fa.accept_17_12_6_10_1_7807 97 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 96 142 282 2 48 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 95 142 282 (accept_3_5 95 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 142 282 2 47 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 142 282 (Polychromatic418967fa.accept_12_9_10_6_1_872 93 142 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 142 282 2 46 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 142 282
  (Polychromatic418967fa.accept_9_1_7_3_1_41 91 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 142 282 2 45 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 142 282 (accept_3_5 89 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 142 282 2 44 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 142 282 (Polychromatic418967fa.accept_9_6_7_3_1_436 87 142 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 142 282 2 43 71 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 142 282
  (Polychromatic418967fa.accept_9_4_7_3_1_43 85 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 142 282 2 42 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 142 282 (accept_3_5 83 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 142 282 2 41 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 142 282 (Polychromatic418967fa.accept_12_9_10_6_1_872 81 142 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 142 282 2 40 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 142 282
  (Polychromatic418967fa.accept_15_4_7_12_1_5538 79 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 142 282 2 39 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 142 282 (accept_3_5 77 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 142 282 2 38 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 142 282 (Polychromatic418967fa.accept_12_3_10_6_1_442 75 142 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 142 282 2 37 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 142 282
  (Polychromatic418967fa.accept_9_1_7_3_1_41 73 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 142 282 2 36 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 142 282 (accept_3_5 71 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 142 282 2 35 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 142 282 (Polychromatic418967fa.accept_9_6_7_3_1_436 69 142 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 142 282 2 34 71 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 142 282
  (Polychromatic418967fa.accept_9_4_7_3_1_43 67 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 142 282 2 33 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 142 282 (accept_3_5 65 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 142 282 2 32 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 142 282 (Polychromatic418967fa.accept_12_3_10_6_1_442 63 142 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 142 282 2 31 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 142 282
  (Polychromatic418967fa.accept_16_13_14_10_1_1669 61 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 142 282 2 30 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 142 282 (accept_3_5 59 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 142 282 2 29 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 142 282 (Polychromatic418967fa.accept_12_9_10_6_1_872 57 142 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 142 282 2 28 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 142 282
  (Polychromatic418967fa.accept_9_1_7_3_1_41 55 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 142 282 2 27 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 142 282 (accept_3_5 53 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 142 282 2 26 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 142 282 (Polychromatic418967fa.accept_9_6_7_3_1_436 51 142 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 142 282 2 25 71 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 142 282
  (Polychromatic418967fa.accept_9_4_7_3_1_43 49 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 142 282 2 24 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 142 282 (accept_3_5 47 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 142 282 2 23 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 142 282 (Polychromatic418967fa.accept_12_9_10_6_1_872 45 142 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 142 282 2 22 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 142 282
  (Polychromatic418967fa.accept_22_21_10_18_1_11241 43 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 142 282 2 21 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 142 282 (accept_3_5 41 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 142 282 2 20 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 142 282 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 142 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 142 282 2 19 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 142 282
  (Polychromatic418967fa.accept_9_1_7_3_1_41 37 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 142 282 2 18 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 142 282 (accept_3_5 35 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 142 282 2 17 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 142 282 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 142 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 142 282 2 16 71 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 142 282
  (Polychromatic418967fa.accept_9_4_7_3_1_43 31 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 142 282 2 15 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 142 282 (accept_3_5 29 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 142 282 2 14 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 142 282 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 142 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 142 282 2 13 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 142 282
  (Polychromatic418967fa.accept_11_3_10_7_1_129 25 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 142 282 2 12 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 142 282 (accept_3_5 23 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 142 282 2 11 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 142 282 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 142 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 142 282 2 10 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 142 282
  (Polychromatic418967fa.accept_9_1_7_3_1_41 19 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 142 282 2 9 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 142 282 (accept_3_5 17 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 142 282 2 8 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 142 282 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 142 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 142 282 2 7 71 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 142 282
  (Polychromatic418967fa.accept_9_4_7_3_1_43 13 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 142 282 2 6 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 142 282 (accept_3_5 11 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 142 282 2 5 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 142 282 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 142 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 142 282 2 4 71 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 142 282
  (Polychromatic418967fa.accept_16_7_14_10_1_3544 7 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 142 282 2 3 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 142 282 (accept_3_5 5 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 142
  282 2 2 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  142 282 (Polychromatic418967fa.accept_11_3_10_7_1_129 3 142 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 142 282 2 1 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 142 282 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 142 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  282)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_282_segment_001)))))))))))))))))))))))))))))))))))))))))


