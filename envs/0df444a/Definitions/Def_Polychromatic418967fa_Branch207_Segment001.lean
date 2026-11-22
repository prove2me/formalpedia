-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch207_Segment001
-- name    : Polychromatic418967fa_Branch207_Segment001
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:34:00.754729+00:00
-- url     : https://prove2.me/theorems/cc02d9c5-a549-4dfc-b977-16d6f5de4552
-- title:
--   Polychromatic branch proof segment
-- statement:
--   Checked segment of the pinned Polychromatic branch proof. Kernel types, definition values and allowed axioms match the original proof.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch207_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_207_segment_001 : allB 163 207 :=
  allB_succ' 46 162 207 (Eq.refl Bool.true) (allA_succ_of_gcd 45 162 207 9 5 18 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 162 207
  (Polychromatic418967fa.accept_10_4_2_7_1_373 44 162 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 162 207 (Polychromatic418967fa.accept_11_10_8_9_1_492 43 162 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 162 207 3 14 54 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 162 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 41
  162 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 162 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 40 162 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 162 207 3 13 54 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 162 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 38 162 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 162 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 37
  162 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 162 207 9 4 18 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 162 207
  (Polychromatic418967fa.accept_10_5_2_7_1_345 35 162 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 162 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 34 162 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 162 207 3 11 54 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 162 207 (Polychromatic418967fa.accept_11_10_8_9_1_492
  32 162 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 162 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 162 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 207 3 10 54 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 162 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 162 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 162 207 (Polychromatic418967fa.accept_12_4_6_3_1_332
  28 162 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 162 207 9 3 18 23
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 162 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 162 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 162 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 162 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 162 207 3 8 54 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 162 207
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 23 162 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 162 207 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 162 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 162 207 3 7 54 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 162 207
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 162 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 162 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 162 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 162 207 9 2 18 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 162 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 17
  162 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 162 207
  (Polychromatic418967fa.accept_12_4_6_3_1_332 16 162 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 162 207 3 5 54 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 162 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 162 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 162 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 162 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 162 207 3 4 54 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 162 207
  (Polychromatic418967fa.accept_17_11_9_3_1_1463 11 162 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 162 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 162 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 162 207 9 1 18 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 162 207 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 162 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 162 207
  (Polychromatic418967fa.accept_13_7_6_12_1_2027 7 162 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 162 207 3 2 54 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 162 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 162 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 162 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 162 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 162 207 3 1 54 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 162 207
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 162 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 162 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 162 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 162 207)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 161 207
  (Eq.refl Bool.true) (allA_succ_of_gcd 46 161 207 23 2 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 161 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 161 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 161 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 161 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 161 207 (accept_3_4 43 161 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 161 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 161 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 161 207 (Polychromatic418967fa.accept_13_2_5_12_1_2043 41 161 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 161 207 (accept_3_4 40 161 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 161 207 (Polychromatic418967fa.accept_17_5_8_3_1_1419 39 161
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 161 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 161 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 161 207 (accept_3_4 37 161 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 161 207 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 161 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 161 207 (Polychromatic418967fa.accept_11_2_7_9_1_890 35 161 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 161 207 (accept_3_4 34 161 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 161 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 161
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 161 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 161 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 161 207 (accept_3_4 31 161 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 161 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 161 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 161 207 (Polychromatic418967fa.accept_15_14_11_12_1_4440 29 161 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 161 207 (accept_3_4 28 161 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 161 207 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 161
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 161 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 161 207 (accept_3_4 25 161 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 161 207 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 161 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 23 161 207 23 1 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 22 161 207 (accept_3_4 22 161 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 161 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 161 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 161 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 161 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 161 207 (accept_3_4 19 161 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 161 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  161 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 161 207
  (Polychromatic418967fa.accept_13_4_5_12_1_751 17 161 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 161 207 (accept_3_4 16 161 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 161 207 (Polychromatic418967fa.accept_13_2_5_12_1_2043 15 161 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 161 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 161 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 161 207 (accept_3_4 13 161 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 161 207 (Polychromatic418967fa.accept_17_12_8_3_1_4646 12 161 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 161 207
  (Polychromatic418967fa.accept_16_11_1_15_1_1123 11 161 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 161 207 (accept_3_4 10 161 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 161 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 161 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 161 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 161 207 (accept_3_4 7 161 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 161 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  161 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 207
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 161 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 161 207 (accept_3_4 4 161 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  161 207 (Polychromatic418967fa.accept_14_3_7_11_1_765 3 161 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 161 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 161 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 161 207 (accept_3_4 1 161 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 161 207))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 160 207 (Eq.refl
  Bool.true) (allA_succ_of_accept 47 160 207 (accept_3_5 47 160 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 160 207 (Polychromatic418967fa.accept_13_7_4_12_1_1341 46 160 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 160 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 160 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 160 207 (accept_3_5 44 160 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 160 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 43
  160 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 160 207
  (Polychromatic418967fa.accept_12_6_4_3_1_361 42 160 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 160 207 (accept_3_5 41 160 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 160 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 160 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 160 207 (Polychromatic418967fa.accept_15_9_10_12_1_1625 39 160 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 160 207 (accept_3_5 38 160 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 160 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 160 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 160 207
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 160 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 160 207 (accept_3_5 35 160 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 160 207 (Polychromatic418967fa.accept_13_8_4_12_1_2753 34 160 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 160 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 160 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 160 207 (accept_3_5 32 160 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 160 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 160 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 160 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 160 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 160 207 (accept_3_5 29 160 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 160 207 (Polychromatic418967fa.accept_13_2_4_12_1_745 28 160 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 160 207 (Polychromatic418967fa.accept_17_10_7_3_1_727 27 160 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 160 207 (accept_3_5 26 160 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 160 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 160 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 160 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 160 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 160 207 (accept_3_5 23 160 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 160 207 (Polychromatic418967fa.accept_15_7_10_12_1_2403 22 160 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 160 207 (Polychromatic418967fa.accept_13_8_4_12_1_2753 21 160 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 160 207 (accept_3_5 20 160 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 160 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 160 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 160 207
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 160 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 160 207 (accept_3_5 17 160 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 160 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 160 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 160 207 (Polychromatic418967fa.accept_13_2_4_12_1_745 15 160 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 160 207 (accept_3_5 14 160 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 160 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 160 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 160 207
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 160 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 160 207 (accept_3_5 11 160 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 160 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 160 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 160 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 160 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 160 207 (accept_3_5 8 160 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 160 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 160 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 160 207
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 160 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 160 207 (accept_3_5 5 160 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  160 207 (Polychromatic418967fa.accept_17_4_7_3_1_1417 4 160 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 160 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 160 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 160 207 (accept_3_5 2 160 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 160 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 160 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160 207))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 49 159 207 (Eq.refl Bool.true) (allA_succ_of_gcd 48 159 207 3 16 53 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 159 207
  (Polychromatic418967fa.accept_18_11_15_9_1_360 47 159 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 159 207 (Polychromatic418967fa.accept_18_10_15_9_1_1054 46 159 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 159 207 3 15 53 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 159 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 44 159 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 159 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 159 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 159 207 3 14 53 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 159 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 41
  159 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 159 207
  (Polychromatic418967fa.accept_11_7_5_9_1_884 40 159 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 159 207 3 13 53 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 159 207 (Polychromatic418967fa.accept_10_8_9_7_1_1118 38 159 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 159 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 159 207 3 12 53 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 159 207 (Polychromatic418967fa.accept_13_9_3_12_1_2025 35 159 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 159 207
  (Polychromatic418967fa.accept_7_6_5_4_1_297 34 159 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 159 207 3 11 53 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 159 207 (Polychromatic418967fa.accept_10_2_9_7_1_720 32 159 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 207
  (Polychromatic418967fa.accept_17_14_6_3_1_2362 31 159 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 159 207 3 10 53 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 159 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 159 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 159 207 (Polychromatic418967fa.accept_10_8_9_7_1_1118
  28 159 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 159 207 3 9 53 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 159 207
  (Polychromatic418967fa.accept_17_9_6_3_1_2398 26 159 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 159 207 (Polychromatic418967fa.accept_15_10_9_12_1_2497 25 159 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 159 207 3 8 53 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 159 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 159 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 159 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 159 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 159 207 3 7 53 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 159 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 20
  159 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 207
  (Polychromatic418967fa.accept_15_4_9_12_1_2495 19 159 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 159 207 3 6 53 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 159 207 (Polychromatic418967fa.accept_13_4_3_12_1_2066 17 159 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 159 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 159 207 3 5 53 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 159 207
  (Polychromatic418967fa.accept_15_14_9_12_1_2498 14 159 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 159 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 159 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 159 207 3 4 53 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 159 207
  (Polychromatic418967fa.accept_18_11_15_9_1_360 11 159 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 159 207 (Polychromatic418967fa.accept_15_10_9_12_1_2497 10 159 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 159 207 3 3 53 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 159 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 8
  159 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 207
  (Polychromatic418967fa.accept_11_7_5_9_1_884 7 159 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 159 207 3 2 53 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 159 207 (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 159 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 207 (Polychromatic418967fa.accept_13_4_3_12_1_2066 4 159
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 159 207 3 1 53 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 159 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 159 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 159 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 159 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 159 207))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 158
  207 (Eq.refl Bool.true) (allA_succ_of_accept 49 158 207 (accept_3_4 49 158 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 158 207 (Polychromatic418967fa.accept_15_3_8_12_1_900 48 158 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 158 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 158 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 158 207 (accept_3_4 46 158 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 158 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 158 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 158 207 (Polychromatic418967fa.accept_13_5_2_12_1_1301 44 158 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 158 207 (accept_3_4 43 158 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 158 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 158
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 158 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 158 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 158 207 (accept_3_4 40 158 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 158 207 (Polychromatic418967fa.accept_10_9_8_7_1_714 39 158 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 158 207 (Polychromatic418967fa.accept_22_16_4_9_1_5663 38 158 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 158 207 (accept_3_4 37 158 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 158 207 (Polychromatic418967fa.accept_13_10_2_12_1_1332 36 158
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 158 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 158 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 158 207 (accept_3_4 34 158 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 158 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 158 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 158 207 (Polychromatic418967fa.accept_13_6_2_12_1_2802 32 158 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 158 207 (accept_3_4 31 158 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 158 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 158
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 158 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 158 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 158 207 (accept_3_4 28 158 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 158 207 (Polychromatic418967fa.accept_13_1_2_12_1_1299 27 158 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 158 207 (Polychromatic418967fa.accept_15_11_8_12_1_4437 26 158 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 158 207 (accept_3_4 25 158 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 158 207 (Polychromatic418967fa.accept_11_2_4_9_1_484 24 158
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 158 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 158 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 158 207 (accept_3_4 22 158 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 158 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 158 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 158 207 (Polychromatic418967fa.accept_15_5_8_12_1_2435 20 158 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 158 207 (accept_3_4 19 158 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 158 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 158
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 158 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 158 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 158 207 (accept_3_4 16 158 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 158 207 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 158 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 158 207 (Polychromatic418967fa.accept_13_1_2_12_1_1299 14 158 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 158 207 (accept_3_4 13 158 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 158 207 (Polychromatic418967fa.accept_19_12_6_17_1_12061 12
  158 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 158 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 158 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 158 207 (accept_3_4 10 158 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  158 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 158 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 158 207 (Polychromatic418967fa.accept_14_8_4_11_1_3035 8 158 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 158 207 (accept_3_4 7 158 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 158 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 158 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 158 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 158 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 158 207 (accept_3_4 4 158 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  158 207 (Polychromatic418967fa.accept_13_3_2_12_1_2797 3 158 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 158 207 (Polychromatic418967fa.accept_11_2_4_9_1_484 2 158 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 158 207 (accept_3_4 1 158 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 158 207)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 157 207
  (Eq.refl Bool.true) (allA_succ_of_accept 50 157 207 (accept_3_5 50 157 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 157 207 (Polychromatic418967fa.accept_14_7_3_11_1_2199 49 157 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 157 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 157 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 157 207 (accept_3_5 47 157 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 157 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 46
  157 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 157 207
  (Polychromatic418967fa.accept_12_9_1_3_1_350 45 157 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 157 207 (accept_3_5 44 157 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 157 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 157 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 157 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 157 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 157 207 (accept_3_5 41 157 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 157 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 157 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 157 207
  (Polychromatic418967fa.accept_11_6_3_9_1_906 39 157 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 157 207 (accept_3_5 38 157 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 157 207 (Polychromatic418967fa.accept_13_11_1_12_1_742 37 157 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 157 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 157 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 157 207 (accept_3_5 35 157 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 157 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 157 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 157 207
  (Polychromatic418967fa.accept_12_9_1_3_1_350 33 157 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 157 207 (accept_3_5 32 157 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 157 207 (Polychromatic418967fa.accept_13_5_1_12_1_740 31 157 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 157 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 157 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 157 207 (accept_3_5 29 157 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 157 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 157 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 157 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 157 207 (accept_3_5 26 157 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 157 207 (Polychromatic418967fa.accept_15_10_7_12_1_2490 25 157 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 157 207 (Polychromatic418967fa.accept_13_11_1_12_1_742 24 157 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 207 (accept_3_5 23 157 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 157 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 157 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 207
  (Polychromatic418967fa.accept_12_9_1_3_1_350 21 157 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 157 207 (accept_3_5 20 157 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 157 207 (Polychromatic418967fa.accept_15_4_7_12_1_5538 19 157 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 157 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 157 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 207 (accept_3_5 17 157 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 157 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 157 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 207 (accept_3_5 14 157 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 157 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 207 (Polychromatic418967fa.accept_16_12_13_15_1_1966 12 157 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 207 (accept_3_5 11 157 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 157 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 207
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 157 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 207 (accept_3_5 8 157 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 207 (Polychromatic418967fa.accept_14_7_3_11_1_2199 7 157 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 157 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 207 (accept_3_5 5 157 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 157 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 207
  (Polychromatic418967fa.accept_15_3_7_12_1_372 3 157 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 207 (accept_3_5 2 157 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 157 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 207))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 156 207 (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 156 207 3 17 52 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 156 207 (Polychromatic418967fa.accept_15_5_6_12_1_916 50 156 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 156 207
  (Polychromatic418967fa.accept_19_11_4_17_1_2617 49 156 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 156 207 3 16 52 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 156 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 156 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 156 207
  (Polychromatic418967fa.accept_18_10_12_9_1_2012 46 156 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 156 207 3 15 52 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 156 207 (Polychromatic418967fa.accept_19_6_4_17_1_6540 44 156 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 156 207
  (Polychromatic418967fa.accept_8_3_4_7_1_475 43 156 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 156 207 3 14 52 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 156 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 156 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 156 207 (Polychromatic418967fa.accept_7_5_2_4_1_126
  40 156 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 156 207 3 13 52 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 156 207
  (Polychromatic418967fa.accept_21_17_9_18_1_7521 38 156 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 156 207 (Polychromatic418967fa.accept_11_4_2_9_1_496 37 156 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 156 207 3 12 52 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 156 207
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 156 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 156 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 156 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 156 207 3 11 52 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 156 207 (Polychromatic418967fa.accept_15_2_6_12_1_1613
  32 156 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 156 207
  (Polychromatic418967fa.accept_10_1_6_7_1_710 31 156 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 156 207 3 10 52 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 156 207 (Polychromatic418967fa.accept_11_7_2_9_1_480 29 156 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 156 207
  (Polychromatic418967fa.accept_18_10_12_9_1_2012 28 156 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 156 207 3 9 52 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 156 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 156 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 156 207
  (Polychromatic418967fa.accept_15_10_6_12_1_1645 25 156 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 156 207 3 8 52 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 156 207 (Polychromatic418967fa.accept_10_3_6_7_1_2188 23 156 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 156 207
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 22 156 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 156 207 3 7 52 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 156 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 156 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 156 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 156 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 156 207 3 6 52 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 156 207
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 17 156 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 156 207 (Polychromatic418967fa.accept_18_16_12_9_1_5504 16 156 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 156 207 3 5 52 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 156 207
  (Polychromatic418967fa.accept_21_14_9_18_1_12132 14 156 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 156 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 156 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 207 3 4 52 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 207
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 156 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 156 207 (Polychromatic418967fa.accept_15_10_6_12_1_1645 10 156 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 156 207 3 3 52 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 156 207 (Polychromatic418967fa.accept_16_8_12_15_1_2005
  8 156 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 156 207
  (Polychromatic418967fa.accept_11_7_2_9_1_480 7 156 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 156 207 3 2 52 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 156 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 156 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 156 207 (Polychromatic418967fa.accept_11_4_2_9_1_496 4 156 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 156 207 3 1 52 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 156 207
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 2 156 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 156 207 (Polychromatic418967fa.accept_10_1_6_7_1_710 1 156 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 156 207)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53
  155 207 (Eq.refl Bool.true) (allA_succ_of_accept 52 155 207 (accept_3_4 52 155 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 155 207 (Polychromatic418967fa.accept_15_6_5_12_1_1642 51 155 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 155 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 155 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 155 207 (accept_3_4 49 155 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 155 207 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 155 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 155 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 155 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 155 207 (accept_3_4 46 155 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 155 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 155 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 155 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 155 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 155 207 (accept_3_4 43 155 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 155 207 (Polychromatic418967fa.accept_10_2_5_7_1_1124 42 155 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 155 207 (Polychromatic418967fa.accept_20_1_15_7_1_3405 41 155 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 155 207 (accept_3_4 40 155 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 155 207 (Polychromatic418967fa.accept_15_9_5_12_1_1640 39 155
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 155 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 155 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 155 207 (accept_3_4 37 155 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 155 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 155 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 155 207 (Polychromatic418967fa.accept_16_3_11_15_1_1963 35 155 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 155 207 (accept_3_4 34 155 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 155 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 155 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 155 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 155 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 155 207 (accept_3_4 31 155 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 155 207 (Polychromatic418967fa.accept_18_12_11_9_1_4257 30 155 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 155 207 (Polychromatic418967fa.accept_27_2_20_18_1_12131 29 155 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 155 207 (accept_3_4 28 155 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 155 207 (Polychromatic418967fa.accept_19_8_3_17_1_5181 27 155
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 155 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 155 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 155 207 (accept_3_4 25 155 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 155 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 155 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 155 207 (Polychromatic418967fa.accept_10_3_5_7_1_330 23 155 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 155 207 (accept_3_4 22 155 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 155 207 (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 155
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 155 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 155 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 155 207 (accept_3_4 19 155 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 155 207 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 155 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 155 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 155 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 155 207 (accept_3_4 16 155 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 155 207 (Polychromatic418967fa.accept_18_15_11_9_1_4256 15 155 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 155 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 155 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 155 207 (accept_3_4 13 155 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 155 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 155 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 155 207 (Polychromatic418967fa.accept_17_11_2_3_1_8468 11 155 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 155 207 (accept_3_4 10 155 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 155 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 155 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 155 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 155 207 (accept_3_4 7 155 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  155 207 (Polychromatic418967fa.accept_15_6_5_12_1_1642 6 155 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 155 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 155 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 155 207 (accept_3_4 4 155 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 155 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 155 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 155 207 (accept_3_4 1 155 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155
  207))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 154 207 (Eq.refl Bool.true)
  (allA_succ_of_accept 53 154 207 (accept_3_5 53 154 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 154 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 52 154 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 154 207 (Polychromatic418967fa.accept_10_1_4_7_1_374 51 154 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 154 207 (accept_3_5 50 154 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 154 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 154 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 154 207
  (Polychromatic418967fa.accept_18_12_10_9_1_5497 48 154 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 154 207 (accept_3_5 47 154 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 154 207 (Polychromatic418967fa.accept_13_7_11_12_1_2051 46 154 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 154 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 45
  154 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 154 207 (accept_3_5 44
  154 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 154 207
  (Polychromatic418967fa.accept_6_1_4_3_1_14 43 154 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 154 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 154 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 154 207 (accept_3_5 41 154 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 154 207 (Polychromatic418967fa.accept_13_1_11_12_1_1322 40 154 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 154 207
  (Polychromatic418967fa.accept_15_9_4_12_1_1611 39 154 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 154 207 (accept_3_5 38 154 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 154 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 154 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 154 207 (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 154 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 154 207 (accept_3_5 35 154 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 154 207 (Polychromatic418967fa.accept_19_15_2_17_1_5163 34 154
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 154 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 154 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 154 207 (accept_3_5 32 154 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 154 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 154 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 154 207 (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 154 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 154 207 (accept_3_5 29 154 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 154 207 (Polychromatic418967fa.accept_19_9_2_17_1_10805 28 154
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 154 207
  (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 154 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 154 207 (accept_3_5 26 154 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 154 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 154 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 154 207 (Polychromatic418967fa.accept_15_9_4_12_1_1611 24 154
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 154 207 (accept_3_5 23 154
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 154 207
  (Polychromatic418967fa.accept_10_2_4_7_1_352 22 154 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 154 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 154 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 154 207 (accept_3_5 20 154 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 154 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 154 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 154 207
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 154 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 154 207 (accept_3_5 17 154 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 154 207 (Polychromatic418967fa.accept_15_1_4_12_1_2401 16 154 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 154 207 (Polychromatic418967fa.accept_17_15_1_3_1_1488 15 154 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 154 207 (accept_3_5 14 154 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 154 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 154 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 154 207
  (Polychromatic418967fa.accept_10_2_4_7_1_352 12 154 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 154 207 (accept_3_5 11 154 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 154 207 (Polychromatic418967fa.accept_13_10_11_12_1_1320 10 154 207 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 154 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 154 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 154 207 (accept_3_5 8 154 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 154 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 154 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 154 207
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 154 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 154 207 (accept_3_5 5 154 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  154 207 (Polychromatic418967fa.accept_13_4_11_12_1_1318 4 154 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 154 207 (Polychromatic418967fa.accept_10_3_4_7_1_353 3 154 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 154 207 (accept_3_5 2 154 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 154 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 154 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 153 207 (Eq.refl Bool.true) (allA_succ_of_gcd
  54 153 207 9 6 17 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 153 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 53 153 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 153 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 153 207 3 17 51 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 153 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 153 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 153 207 (Polychromatic418967fa.accept_12_1_9_3_1_370 49 153 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 153 207 3 16 51 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 153 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 47
  153 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 153 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 153 207 9 5 17 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 153 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 153 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 153 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 43 153
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 153 207 3 14 51 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 153 207
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 41 153 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 153 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 153 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 153 207 3 13 51 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 153 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  153 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 153 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 153 207 9 4 17 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 153 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 153 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 153 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 153 207 3 11 51 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 153 207
  (Polychromatic418967fa.accept_13_6_10_12_1_2049 32 153 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 153 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 153 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 153 207 3 10 51 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 153 207
  (Polychromatic418967fa.accept_12_5_9_3_1_85 29 153 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 153 207 (Polychromatic418967fa.accept_13_2_10_12_1_757 28 153 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 153 207 9 3 17 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 153 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  153 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 207
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 153 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 153 207 3 8 51 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 153 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 153 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 153 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 153 207 3 7 51 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 153 207
  (Polychromatic418967fa.accept_13_7_10_12_1_2047 20 153 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 153 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 153 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 153 207 9 2 17 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 153 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 153 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 153 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 153 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 153 207 3 5 51 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 153 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  153 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 207
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 153 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 153 207 3 4 51 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 153 207 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 153 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 153 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 153 207 9 1 17 23 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 153 207
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 153 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 153 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 153 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 153 207 3 2 51 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 153 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 153 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 207
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 4 153 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 153 207 3 1 51 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 153 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 153 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 207 (Polychromatic418967fa.accept_11_1_10_9_1_871 1 153 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 152 207 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 152 207 (accept_3_4 55 152 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 152 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 54 152 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 152 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 152 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 152 207 (accept_3_4 52 152 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 152 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 152 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 152 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 50 152 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 152 207 (accept_3_4 49 152 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 152 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 152 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 152 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 152 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 152 207 (accept_3_4 46 152 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 152 207 (Polychromatic418967fa.accept_10_5_2_7_1_345 45 152 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 152 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 44 152 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 152 207 (accept_3_4 43 152 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 152 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 152 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 152 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 152 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 152 207 (accept_3_4 40 152 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 152 207 (Polychromatic418967fa.accept_10_9_2_7_1_1096 39 152 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 152 207
  (Polychromatic418967fa.accept_17_4_16_3_1_4620 38 152 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 152 207 (accept_3_4 37 152 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 152 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 152 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 152 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 152 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 152 207 (accept_3_4 34 152 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 152 207 (Polychromatic418967fa.accept_15_3_2_12_1_2469 33 152 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 152 207
  (Polychromatic418967fa.accept_21_11_5_18_1_5998 32 152 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 152 207 (accept_3_4 31 152 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 152 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 152 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 152 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 152 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 152 207 (accept_3_4 28 152 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 152 207 (Polychromatic418967fa.accept_7_6_5_4_1_297
  27 152 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 152 207
  (Polychromatic418967fa.accept_20_6_12_7_1_12130 26 152 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 152 207 (accept_3_4 25 152 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 152 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 152 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 152 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 152 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 152 207 (accept_3_4 22 152 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 152 207
  (Polychromatic418967fa.accept_13_8_9_12_1_2813 21 152 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 152 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 152 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 152 207 (accept_3_4 19 152 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 152 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 152 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 152 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 17
  152 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 152 207 (accept_3_4 16
  152 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 152 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 152 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 152 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 152 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 152 207 (accept_3_4 13 152 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 152 207 (Polychromatic418967fa.accept_16_12_8_15_1_5119 12 152 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 152 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 152 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 152 207 (accept_3_4 10 152 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  152 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 152 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 152 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 152 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 152 207 (accept_3_4 7 152 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 152 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 152 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 152 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 152 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 152 207 (accept_3_4 4 152 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  152 207 (Polychromatic418967fa.accept_13_3_9_12_1_2062 3 152 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 152 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 152 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 152 207 (accept_3_4 1 152 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 152 207)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 151 207
  (Eq.refl Bool.true) (allA_succ_of_accept 56 151 207 (accept_3_5 56 151 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 151 207 (Polychromatic418967fa.accept_21_13_4_18_1_7553 55 151 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 151 207 (Polychromatic418967fa.accept_10_4_1_7_1_371
  54 151 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 151 207 (accept_3_5 53
  151 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 151 207
  (Polychromatic418967fa.accept_6_4_1_3_1_77 52 151 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 151 207 (Polychromatic418967fa.accept_16_3_7_15_1_1130 51 151 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 151 207 (accept_3_5 50 151 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 151 207 (Polychromatic418967fa.accept_13_10_8_12_1_2032 49 151 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 151 207
  (Polychromatic418967fa.accept_13_9_8_12_1_2031 48 151 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 151 207 (accept_3_5 47 151 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 151 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 151 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 151 207 (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 151 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 151 207 (accept_3_5 44 151 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 151 207 (Polychromatic418967fa.accept_11_10_8_9_1_492 43 151
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 151 207
  (Polychromatic418967fa.accept_18_6_7_9_1_4250 42 151 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 151 207 (accept_3_5 41 151 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 151 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 151 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 151 207 (Polychromatic418967fa.accept_18_3_7_9_1_5486 39 151 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 151 207 (accept_3_5 38 151 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 151 207 (Polychromatic418967fa.accept_24_13_7_15_1_12129 37
  151 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 151 207
  (Polychromatic418967fa.accept_10_6_1_7_1_342 36 151 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 151 207 (accept_3_5 35 151 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 151 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 151 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 151 207 (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 151 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 151 207 (accept_3_5 32 151 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 151 207 (Polychromatic418967fa.accept_13_5_8_12_1_2759 31 151
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 151 207
  (Polychromatic418967fa.accept_13_4_8_12_1_3526 30 151 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 151 207 (accept_3_5 29 151 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 151 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 151 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 151 207 (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 151 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 151 207 (accept_3_5 26 151 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 151 207 (Polychromatic418967fa.accept_19_6_18_17_1_9518 25 151
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 151 207
  (Polychromatic418967fa.accept_10_4_1_7_1_371 24 151 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 151 207 (accept_3_5 23 151 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 151 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 151 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 151 207 (Polychromatic418967fa.accept_11_10_8_9_1_492 21 151 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 151 207 (accept_3_5 20 151 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 151 207 (Polychromatic418967fa.accept_15_4_1_12_1_914 19 151
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 151 207
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 18 151 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 151 207 (accept_3_5 17 151 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 151 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 151 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 151 207 (Polychromatic418967fa.accept_25_15_1_7_1_12128 15 151 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 151 207 (accept_3_5 14 151 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 151 207 (Polychromatic418967fa.accept_15_13_1_12_1_1638 13 151
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 151 207
  (Polychromatic418967fa.accept_17_12_15_3_1_7168 12 151 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 151 207 (accept_3_5 11 151 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 151 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 151 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 207 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 151 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 207 (accept_3_5 8 151 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 151 207 (Polychromatic418967fa.accept_13_7_8_12_1_2810
  7 151 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 151 207
  (Polychromatic418967fa.accept_10_6_1_7_1_342 6 151 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 151 207 (accept_3_5 5 151 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  151 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 151 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 151 207 (Polychromatic418967fa.accept_16_3_7_15_1_1130 3 151 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 207 (accept_3_5 2 151 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 207 (Polychromatic418967fa.accept_13_1_8_12_1_2045 1 151
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 150 207 (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 150 207 3 19 50 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 150 207 (Polychromatic418967fa.accept_12_8_6_3_1_366 56 150 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 150 207 (Polychromatic418967fa.accept_7_6_3_4_1_294
  55 150 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 150 207 3 18 50 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 150 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 150 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 150 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 52 150 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 150 207 3 17 50 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 150 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 50
  150 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 150 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 150 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 150 207 3 16 50 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 150 207 (Polychromatic418967fa.accept_13_8_7_12_1_3637 47 150 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 150 207
  (Polychromatic418967fa.accept_11_2_7_9_1_890 46 150 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 150 207 3 15 50 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 150 207 (Polychromatic418967fa.accept_12_8_6_3_1_366 44 150 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 150 207 (Polychromatic418967fa.accept_7_1_3_4_1_128
  43 150 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 150 207 3 14 50 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 150 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 150 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 150 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 150 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 150 207 3 13 50 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 150 207 (Polychromatic418967fa.accept_11_5_7_9_1_2696
  38 150 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 150 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 150 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 207 3 12 50 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 150 207 (Polychromatic418967fa.accept_11_2_7_9_1_890 35 150 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 150 207 (Polychromatic418967fa.accept_7_6_3_4_1_294
  34 150 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 150 207 3 11 50 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 150 207
  (Polychromatic418967fa.accept_12_8_6_3_1_366 32 150 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 150 207 (Polychromatic418967fa.accept_13_5_7_12_1_2757 31 150 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 150 207 3 10 50 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 150 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 29
  150 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 150 207
  (Polychromatic418967fa.accept_12_4_6_3_1_332 28 150 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 150 207 3 9 50 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 150 207 (Polychromatic418967fa.accept_12_2_6_3_1_331 26 150 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 150 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 150 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 150 207 3 8 50 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 150 207
  (Polychromatic418967fa.accept_13_10_7_12_1_2782 23 150 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 150 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 150 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 150 207 3 7 50 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 150 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 150 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 150 207 (Polychromatic418967fa.accept_13_6_7_12_1_3504 19 150 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 150 207 3 6 50 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 150 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 17
  150 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 150 207
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 16 150 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 150 207 3 5 50 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 150 207 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 150 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 150 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 150 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 207 3 4 50 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 207
  (Polychromatic418967fa.accept_13_11_7_12_1_2758 11 150 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 150 207 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 150 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 150 207 3 3 50 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 150 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 150 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 150 207 (Polychromatic418967fa.accept_14_7_10_11_1_8112 7 150 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 207 3 2 50 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 150 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 150 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 150 207
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 150 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 150 207 3 1 50 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 150 207 (Polychromatic418967fa.accept_11_2_7_9_1_890 2 150 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 150 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 149 207 (Eq.refl Bool.true)
  (allA_succ_of_accept 58 149 207 (accept_3_4 58 149 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 149 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 57 149 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 149 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 149 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 149 207 (accept_3_4 55 149 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 149 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 149 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 149 207
  (Polychromatic418967fa.accept_27_26_14_18_1_10164 53 149 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 149 207 (accept_3_4 52 149 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 149 207 (Polychromatic418967fa.accept_18_15_5_9_1_5529 51 149 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 149 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 149 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 149 207 (accept_3_4 49 149 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 149 207 (Polychromatic418967fa.accept_7_6_2_4_1_291
  48 149 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 149 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 47 149 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 149 207 (accept_3_4 46 149 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 149 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 149 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 149 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 149 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 149 207 (accept_3_4 43 149 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 149 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 149 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 149 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 149 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 149 207 (accept_3_4 40 149 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 149 207 (Polychromatic418967fa.accept_15_9_14_12_1_913 39 149 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 149 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 149 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 149 207 (accept_3_4 37 149 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 149 207 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 149 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 149 207
  (Polychromatic418967fa.accept_26_9_19_25_1_12104 35 149 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 149 207 (accept_3_4 34 149 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 149 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 149 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 149 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 149 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 149 207 (accept_3_4 31 149 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 149 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 30
  149 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 149 207
  (Polychromatic418967fa.accept_25_4_24_7_1_12127 29 149 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 149 207 (accept_3_4 28 149 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 149 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 149 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 149 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 149 207 (accept_3_4 25 149 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 149 207
  (Polychromatic418967fa.accept_15_9_14_12_1_913 24 149 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 149 207 (Polychromatic418967fa.accept_13_10_6_12_1_2780 23 149 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 207 (accept_3_4 22 149 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 149 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 149 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 149 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 149 207 (accept_3_4 19 149 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 149 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 149 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 149 207 (Polychromatic418967fa.accept_15_2_14_12_1_2453 17 149 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 207 (accept_3_4 16 149 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 207 (Polychromatic418967fa.accept_13_2_6_12_1_1334 15 149
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 149 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 149 207 (accept_3_4 13 149 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 149 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 149 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 149 207 (Polychromatic418967fa.accept_15_11_14_12_1_2458 11 149 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 207 (accept_3_4 10 149 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 149 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 149 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 207 (accept_3_4 7 149 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 149 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 149 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 207 (accept_3_4 4 149 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 207 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 149 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 149 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 207 (accept_3_4 1 149 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 148 207 (Eq.refl Bool.true)
  (allA_succ_of_accept 59 148 207 (accept_3_5 59 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 148 207 (Polychromatic418967fa.accept_13_6_5_12_1_307 58 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 148 207 (Polychromatic418967fa.accept_20_17_8_7_1_7859 57 148 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 148 207 (accept_3_5 56 148 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 148 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 148 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 148 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 54 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 148 207 (accept_3_5 53 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 148 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 148 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 148 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 148 207 (accept_3_5 50 148 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 148 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 148 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 148 207
  (Polychromatic418967fa.accept_15_3_13_12_1_348 48 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 148 207 (accept_3_5 47 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 148 207 (Polychromatic418967fa.accept_13_7_5_12_1_1305 46 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 148 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 148 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 148 207 (accept_3_5 44 148 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 148 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 148 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 148 207
  (Polychromatic418967fa.accept_12_6_4_3_1_361 42 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 148 207 (accept_3_5 41 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 148 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 148 207 (Polychromatic418967fa.accept_10_9_8_7_1_714 39 148 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 148 207 (accept_3_5 38 148 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 148 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 148 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 148 207
  (Polychromatic418967fa.accept_21_15_1_18_1_3066 36 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 148 207 (accept_3_5 35 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 148 207 (Polychromatic418967fa.accept_13_8_5_12_1_2755 34 148 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 148 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 148 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 148 207 (accept_3_5 32 148 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 148 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 31
  148 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 148 207
  (Polychromatic418967fa.accept_12_6_4_3_1_361 30 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 148 207 (accept_3_5 29 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 148 207 (Polychromatic418967fa.accept_13_2_5_12_1_2043 28 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 148 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 148 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 148 207 (accept_3_5 26 148 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 148 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 148 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 148 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 148 207 (accept_3_5 23 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 148 207 (Polychromatic418967fa.accept_19_3_15_17_1_12070 22 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 148 207 (Polychromatic418967fa.accept_13_8_5_12_1_2755 21 148 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 148 207 (accept_3_5 20 148 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 148 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19
  148 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 148 207
  (Polychromatic418967fa.accept_11_7_5_9_1_884 18 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 148 207 (accept_3_5 17 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 148 207 (Polychromatic418967fa.accept_15_1_13_12_1_347 16 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 148 207 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 148 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 148 207 (accept_3_5 14 148 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 148 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 148 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 148 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 148 207 (accept_3_5 11 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 148 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 148 207 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 148 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 148 207 (accept_3_5 8 148 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 148 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 148 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 148 207
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 148 207 (accept_3_5 5 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  148 207 (Polychromatic418967fa.accept_13_4_5_12_1_751 4 148 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 148 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 148 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 148 207 (accept_3_5 2 148 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 148 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 148 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 147 207 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 147 207 3 20 49 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 147 207 (Polychromatic418967fa.accept_13_7_4_12_1_1341 59 147 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 147 207
  (Polychromatic418967fa.accept_19_1_14_17_1_6605 58 147 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 57 147 207 3 19 49 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 56 147 207 (Polychromatic418967fa.accept_18_2_3_9_1_1996 56 147 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 147 207
  (Polychromatic418967fa.accept_13_3_4_12_1_36 55 147 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 147 207 3 18 49 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 147 207 (Polychromatic418967fa.accept_17_2_11_3_1_4654 53 147 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 147 207
  (Polychromatic418967fa.accept_8_4_3_7_1_491 52 147 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 147 207 3 17 49 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 147 207 (Polychromatic418967fa.accept_13_11_4_12_1_3585 50 147 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 147 207
  (Polychromatic418967fa.accept_18_13_3_9_1_4233 49 147 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 147 207 3 16 49 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 147 207 (Polychromatic418967fa.accept_13_8_4_12_1_2753 47 147 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 147 207
  (Polychromatic418967fa.accept_11_2_4_9_1_484 46 147 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 147 207 3 15 49 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 147 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 44 147 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 207
  (Polychromatic418967fa.accept_16_11_3_15_1_1989 43 147 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 147 207 3 14 49 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 147 207 (Polychromatic418967fa.accept_13_2_4_12_1_745 41 147 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 207
  (Polychromatic418967fa.accept_19_2_14_17_1_700 40 147 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 147 207 3 13 49 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 147 207 (Polychromatic418967fa.accept_14_10_7_11_1_3015 38 147 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 207
  (Polychromatic418967fa.accept_13_11_4_12_1_3585 37 147 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 147 207 3 12 49 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 147 207 (Polychromatic418967fa.accept_11_2_4_9_1_484 35 147 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 207
  (Polychromatic418967fa.accept_13_8_4_12_1_2753 34 147 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 147 207 3 11 49 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 147 207 (Polychromatic418967fa.accept_14_4_7_11_1_790 32 147 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 207
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 31 147 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 147 207 3 10 49 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 147 207 (Polychromatic418967fa.accept_13_3_4_12_1_36 29 147 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 207 (Polychromatic418967fa.accept_8_4_3_7_1_491
  28 147 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 147 207 3 9 49 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 147 207
  (Polychromatic418967fa.accept_17_9_11_3_1_2353 26 147 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 147 207 (Polychromatic418967fa.accept_18_7_3_9_1_1020 25 147 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 147 207 3 8 49 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 147 207 (Polychromatic418967fa.accept_16_7_3_15_1_2940
  23 147 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 207
  (Polychromatic418967fa.accept_19_3_14_17_1_6603 22 147 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 147 207 3 7 49 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 147 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 147 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 207
  (Polychromatic418967fa.accept_17_2_11_3_1_4654 19 147 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 147 207 3 6 49 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 147 207 (Polychromatic418967fa.accept_14_3_7_11_1_765 17 147 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 207 (Polychromatic418967fa.accept_13_3_4_12_1_36 16 147
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 147 207 3 5 49 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 147 207
  (Polychromatic418967fa.accept_17_14_11_3_1_4653 14 147 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 147 207 (Polychromatic418967fa.accept_11_2_4_9_1_484 13 147 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 147 207 3 4 49 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 147 207
  (Polychromatic418967fa.accept_13_11_4_12_1_3585 11 147 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 147 207 (Polychromatic418967fa.accept_14_10_7_11_1_3015 10 147 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 147 207 3 3 49 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 147 207
  (Polychromatic418967fa.accept_13_8_4_12_1_2753 8 147 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 147 207 (Polychromatic418967fa.accept_13_7_4_12_1_1341 7 147 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 147 207 3 2 49 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 147 207 (Polychromatic418967fa.accept_13_5_4_12_1_2058 5 147 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 207
  (Polychromatic418967fa.accept_8_4_3_7_1_491 4 147 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 147 207 3 1 49 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 147 207 (Polychromatic418967fa.accept_11_2_4_9_1_484 2 147 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 207 (Polychromatic418967fa.accept_18_1_3_9_1_328 1 147 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 146 207 (Eq.refl Bool.true)
  (allA_succ_of_accept 61 146 207 (accept_3_4 61 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 146 207 (Polychromatic418967fa.accept_16_12_2_15_1_490 60 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 146 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 146 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 146 207 (accept_3_4 58 146 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 146 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 146 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 146 207
  (Polychromatic418967fa.accept_13_4_3_12_1_2066 56 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 146 207 (accept_3_4 55 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 146 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 146 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 146 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 146 207 (accept_3_4 52 146 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 146 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 146 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 146 207
  (Polychromatic418967fa.accept_11_6_3_9_1_906 50 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 146 207 (accept_3_4 49 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 146 207 (Polychromatic418967fa.accept_13_9_3_12_1_2025 48 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 146 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 146 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 146 207 (accept_3_4 46 146 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 146 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 146 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 146 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 44 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 146 207 (accept_3_4 43 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 146 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 146 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 146 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 146 207 (accept_3_4 40 146 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 146 207 (Polychromatic418967fa.accept_11_6_3_9_1_906 39 146 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 146 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 38 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 146 207 (accept_3_4 37 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 146 207 (Polychromatic418967fa.accept_20_16_6_7_1_10779 36 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 146 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 146 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 146 207 (accept_3_4 34 146 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 146 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 146 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 146 207
  (Polychromatic418967fa.accept_20_12_6_7_1_7875 32 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 146 207 (accept_3_4 31 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 146 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 146 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 146 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 146 207 (accept_3_4 28 146 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 146 207 (Polychromatic418967fa.accept_21_6_20_18_1_12126 27 146 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 146 207
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 146 207 (accept_3_4 25 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 146 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 146 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 146 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 146 207 (accept_3_4 22 146 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 146 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 146 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 146 207
  (Polychromatic418967fa.accept_22_20_14_9_1_12125 20 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 146 207 (accept_3_4 19 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 146 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 146 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 146 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 146 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 146 207 (accept_3_4 16 146 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 146 207 (Polychromatic418967fa.accept_13_2_3_12_1_735
  15 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 146 207
  (Polychromatic418967fa.accept_15_14_11_12_1_4440 14 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 146 207 (accept_3_4 13 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 146 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 146 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 146 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 146 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 146 207 (accept_3_4 10 146 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 146 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9
  146 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 146 207
  (Polychromatic418967fa.accept_15_8_11_12_1_1626 8 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 146 207 (accept_3_4 7 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  146 207 (Polychromatic418967fa.accept_11_6_3_9_1_906 6 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 146 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 146 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 146 207 (accept_3_4 4 146 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 146 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 146 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 146 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 146 207 (accept_3_4 1 146 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 145 207 (Eq.refl Bool.true)
  (allA_succ_of_accept 62 145 207 (accept_3_5 62 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 145 207 (Polychromatic418967fa.accept_17_10_9_3_1_7144 61 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 145 207 (Polychromatic418967fa.accept_18_6_1_9_1_5551 60 145 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 145 207 (accept_3_5 59 145 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 145 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 145 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 145 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 57 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 145 207 (accept_3_5 56 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 145 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 145 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 145 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 145 207 (accept_3_5 53 145 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 145 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 145 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 145 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 145 207 (accept_3_5 50 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 145 207 (Polychromatic418967fa.accept_13_10_2_12_1_1332 49 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 145 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 145 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 145 207 (accept_3_5 47 145 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 145 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 145 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 145 207
  (Polychromatic418967fa.accept_12_9_1_3_1_350 45 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 145 207 (accept_3_5 44 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 145 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 145 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 145 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 145 207 (accept_3_5 41 145 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 145 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 145 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 145 207
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 39 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 145 207 (accept_3_5 38 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 145 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 145 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 145 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 145 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 145 207 (accept_3_5 35 145 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 145 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 34
  145 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 145 207
  (Polychromatic418967fa.accept_10_3_5_7_1_330 33 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 145 207 (accept_3_5 32 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 145 207 (Polychromatic418967fa.accept_13_5_2_12_1_1301 31 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 145 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 145 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 145 207 (accept_3_5 29 145 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 145 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 145 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 145 207
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 145 207 (accept_3_5 26 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 145 207 (Polychromatic418967fa.accept_19_6_12_17_1_12050 25 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 145 207 (Polychromatic418967fa.accept_15_9_10_12_1_1625 24 145 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 145 207 (accept_3_5 23 145 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 145 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 22
  145 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 207
  (Polychromatic418967fa.accept_12_9_1_3_1_350 21 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 145 207 (accept_3_5 20 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 145 207 (Polychromatic418967fa.accept_13_6_2_12_1_2802 19 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 145 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 145 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 207 (accept_3_5 17 145 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 145 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 145 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 145 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 145 207 (accept_3_5 14 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 145 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 145 207 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 145 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 207 (accept_3_5 11 145 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 145 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 145 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 145 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 145 207 (accept_3_5 8 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  145 207 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 145 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 145 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 145 207 (accept_3_5 5 145 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 145 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 145 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 145 207
  (Polychromatic418967fa.accept_10_3_5_7_1_330 3 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 145 207 (accept_3_5 2 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  145 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 145 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 145 207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 144 207
  (Eq.refl Bool.true) (allA_succ_of_gcd 63 144 207 9 7 16 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 144 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 62 144 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 144 207
  (Polychromatic418967fa.accept_10_1_4_7_1_374 61 144 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 144 207 3 20 48 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 144 207 (Polychromatic418967fa.accept_15_14_9_12_1_2498 59 144 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 144 207
  (Polychromatic418967fa.accept_27_4_9_18_1_12124 58 144 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 57 144 207 3 19 48 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 56 144 207 (Polychromatic418967fa.accept_17_5_8_3_1_1419 56 144 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 144 207
  (Polychromatic418967fa.accept_15_10_9_12_1_2497 55 144 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 144 207 9 6 16 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 144 207 (Polychromatic418967fa.accept_10_3_4_7_1_353 53 144 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 144 207
  (Polychromatic418967fa.accept_10_2_4_7_1_352 52 144 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 144 207 3 17 48 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 144 207 (Polychromatic418967fa.accept_13_11_1_12_1_742 50 144 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 144 207
  (Polychromatic418967fa.accept_14_7_4_11_1_3038 49 144 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 144 207 3 16 48 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 144 207 (Polychromatic418967fa.accept_13_8_1_12_1_762 47 144 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 144 207
  (Polychromatic418967fa.accept_17_12_8_3_1_4646 46 144 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 144 207 9 5 16 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 144 207 (Polychromatic418967fa.accept_13_5_1_12_1_740 44 144 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 144 207 (Polychromatic418967fa.accept_10_3_4_7_1_353 43 144
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 144 207 3 14 48 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 144 207
  (Polychromatic418967fa.accept_10_1_4_7_1_374 41 144 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 144 207 (Polychromatic418967fa.accept_15_10_9_12_1_2497 40 144 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 144 207 3 13 48 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 144 207
  (Polychromatic418967fa.accept_25_13_19_7_1_6688 38 144 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 144 207 (Polychromatic418967fa.accept_13_11_1_12_1_742 37 144 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 144 207 9 4 16 23 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 144 207
  (Polychromatic418967fa.accept_14_7_4_11_1_3038 35 144 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 144 207 (Polychromatic418967fa.accept_13_8_1_12_1_762 34 144 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 144 207 3 11 48 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 144 207 (Polychromatic418967fa.accept_10_2_4_7_1_352
  32 144 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 144 207
  (Polychromatic418967fa.accept_10_1_4_7_1_374 31 144 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 144 207 3 10 48 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 144 207 (Polychromatic418967fa.accept_14_1_4_11_1_3036 29 144 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 144 207
  (Polychromatic418967fa.accept_13_2_1_12_1_1326 28 144 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 144 207 9 3 16 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 144 207 (Polychromatic418967fa.accept_25_1_19_7_1_12123 26 144 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 144 207
  (Polychromatic418967fa.accept_15_10_9_12_1_2497 25 144 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 144 207 3 8 48 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 144 207 (Polychromatic418967fa.accept_10_3_4_7_1_353 23 144 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 144 207
  (Polychromatic418967fa.accept_10_2_4_7_1_352 22 144 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 144 207 3 7 48 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 144 207 (Polychromatic418967fa.accept_15_5_9_12_1_1599 20 144 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 144 207 (Polychromatic418967fa.accept_15_4_9_12_1_2495 19 144
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 144 207 9 2 16 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 144 207
  (Polychromatic418967fa.accept_20_17_4_7_1_4808 17 144 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 144 207 (Polychromatic418967fa.accept_25_16_19_7_1_12122 16 144 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 144 207 3 5 48 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 144 207
  (Polychromatic418967fa.accept_15_14_9_12_1_2498 14 144 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 144 207 (Polychromatic418967fa.accept_10_3_4_7_1_353 13 144 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 207 3 4 48 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 207
  (Polychromatic418967fa.accept_10_1_4_7_1_374 11 144 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 144 207 (Polychromatic418967fa.accept_11_10_1_9_1_2060 10 144 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 144 207 9 1 16 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 144 207 (Polychromatic418967fa.accept_13_8_1_12_1_762 8 144 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 144 207
  (Polychromatic418967fa.accept_14_7_4_11_1_3038 7 144 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 144 207 3 2 48 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 144 207 (Polychromatic418967fa.accept_13_5_1_12_1_740 5 144 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 144 207 (Polychromatic418967fa.accept_15_4_9_12_1_2495 4 144
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 144 207 3 1 48 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 144 207
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 144 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 144 207 (Polychromatic418967fa.accept_10_1_4_7_1_374 1 144 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 144 207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 65 143 207 (Eq.refl Bool.true) (allA_succ_of_accept 64 143 207 (accept_3_4 64 143 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 143 207 (Polychromatic418967fa.accept_14_7_3_11_1_2199 63 143 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 143 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 62 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 143 207 (accept_3_4 61 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 143 207 (Polychromatic418967fa.accept_22_16_11_9_1_12121 60 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 59 143 207 (Polychromatic418967fa.accept_19_2_10_17_1_3876 59 143 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 143 207 (accept_3_4 58 143 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 143 207 (Polychromatic418967fa.accept_7_1_3_4_1_128
  57 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 143 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 143 207 (accept_3_4 55 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 143 207 (Polychromatic418967fa.accept_10_4_3_7_1_1110 54 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 143 207 (Polychromatic418967fa.accept_19_15_10_17_1_3859 53 143 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 143 207 (accept_3_4 52 143 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 143 207 (Polychromatic418967fa.accept_18_15_17_9_1_4200 51 143
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 143 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 143 207 (accept_3_4 49 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 143 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 143 207 (Polychromatic418967fa.accept_22_3_11_9_1_12102 47 143 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 143 207 (accept_3_4 46 143 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 143 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 143
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 143 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 143 207 (accept_3_4 43 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 143 207 (Polychromatic418967fa.accept_19_4_10_17_1_5194 42 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 143 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 143 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 143 207 (accept_3_4 40 143 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 143 207 (Polychromatic418967fa.accept_19_1_10_17_1_5188 39 143 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 143 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 143 207 (accept_3_4 37 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 143 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 143 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 143 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 143 207 (accept_3_4 34 143 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 143 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 143
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 143 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 143 207 (accept_3_4 31 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 143 207 (Polychromatic418967fa.accept_18_12_17_9_1_5513 30 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 143 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 143 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 143 207 (accept_3_4 28 143 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 143 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 143 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 143 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 143 207 (accept_3_4 25 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 143 207 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 143 207 (Polychromatic418967fa.accept_19_4_10_17_1_5194 23 143 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 143 207 (accept_3_4 22 143 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 143 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 143
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 143 207 (accept_3_4 19 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 143 207 (Polychromatic418967fa.accept_15_3_8_12_1_900 18 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 143 207 (Polychromatic418967fa.accept_22_17_11_9_1_10636 17 143 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 207 (accept_3_4 16 143 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 143 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 143 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 143 207 (accept_3_4 13 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 143 207 (Polychromatic418967fa.accept_17_12_7_3_1_1498 12 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 143 207 (Polychromatic418967fa.accept_15_11_8_12_1_4437 11 143 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 207 (accept_3_4 10 143 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 143 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 143 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 143 207 (accept_3_4 7 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  143 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 143 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 143 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 207 (accept_3_4 4 143 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 207 (Polychromatic418967fa.accept_15_3_8_12_1_900 3 143 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 207 (accept_3_4 1 143 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 142 207 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 142 207 (accept_3_5 65 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 142 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 64 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 142 207 (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 142 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 142 207 (accept_3_5 62 142 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 142 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 142 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 142 207
  (Polychromatic418967fa.accept_17_9_6_3_1_2398 60 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 142 207 (accept_3_5 59 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 142 207 (Polychromatic418967fa.accept_16_10_14_15_1_2933 58 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 142 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 142 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 142 207 (accept_3_5 56 142 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 142 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 142 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 142 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 54 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 142 207 (accept_3_5 53 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 142 207 (Polychromatic418967fa.accept_11_8_10_9_1_1401 52 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 142 207 (Polychromatic418967fa.accept_14_9_2_11_1_780 51 142 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 142 207 (accept_3_5 50 142 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 142 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 142 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 142 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 142 207 (accept_3_5 47 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 142 207 (Polychromatic418967fa.accept_19_8_9_17_1_5151 46 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 142 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 142 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 142 207 (accept_3_5 44 142 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 142 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 142 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 142 207
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 142 207 (accept_3_5 41 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 142 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 142 207 (Polychromatic418967fa.accept_10_9_2_7_1_1096 39 142 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 142 207 (accept_3_5 38 142 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 142 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 142 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 142 207
  (Polychromatic418967fa.accept_15_6_7_12_1_869 36 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 142 207 (accept_3_5 35 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 142 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 142 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 142 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 142 207 (accept_3_5 32 142 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 142 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 142 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 142 207
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 30 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 142 207 (accept_3_5 29 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 142 207 (Polychromatic418967fa.accept_26_2_12_25_1_12120 28 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 142 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 142 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 142 207 (accept_3_5 26 142 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 142 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 142 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 142 207
  (Polychromatic418967fa.accept_10_4_2_7_1_373 24 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 142 207 (accept_3_5 23 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 142 207 (Polychromatic418967fa.accept_17_5_6_3_1_4640 22 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 142 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 142 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 142 207 (accept_3_5 20 142 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 142 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 142 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 142 207
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 142 207 (accept_3_5 17 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 142 207 (Polychromatic418967fa.accept_25_16_17_7_1_12119 16 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 142 207 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 142 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 142 207 (accept_3_5 14 142 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 142 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 142 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 142 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 142 207 (accept_3_5 11 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 142 207 (Polychromatic418967fa.accept_15_10_7_12_1_2490 10 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 142 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 142 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 142 207 (accept_3_5 8 142 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 142 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 142 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 142 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 142 207 (accept_3_5 5 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  142 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 142 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 142 207 (Polychromatic418967fa.accept_15_3_7_12_1_372 3 142 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 142 207 (accept_3_5 2 142 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 142 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 142 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 141 207 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 141 207 3 22 47 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 141 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 65 141 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 141 207 (Polychromatic418967fa.accept_10_4_1_7_1_371
  64 141 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 141 207 3 21 47 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 141 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 141 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 141 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 61 141 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 141 207 3 20 47 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 141 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 59
  141 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 141 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 141 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 141 207 3 19 47 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 141 207 (Polychromatic418967fa.accept_10_6_1_7_1_342 56 141 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 207 (Polychromatic418967fa.accept_12_7_9_3_1_767
  55 141 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 141 207 3 18 47 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 141 207
  (Polychromatic418967fa.accept_12_5_9_3_1_85 53 141 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 141 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 141 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 141 207 3 17 47 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 141 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 50
  141 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 207
  (Polychromatic418967fa.accept_12_1_9_3_1_370 49 141 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 141 207 3 16 47 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 141 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 141 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 141 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 46
  141 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 141 207 3 15 47 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 141 207
  (Polychromatic418967fa.accept_10_4_1_7_1_371 44 141 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 141 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 43 141 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 141 207 3 14 47 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 141 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 41
  141 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 141 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 40 141 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 141 207 3 13 47 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 141 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 141 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 207 (Polychromatic418967fa.accept_12_1_9_3_1_370
  37 141 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 141 207 3 12 47 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 141 207
  (Polychromatic418967fa.accept_12_11_9_3_1_792 35 141 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 141 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 141 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 141 207 3 11 47 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 141 207 (Polychromatic418967fa.accept_14_4_1_11_1_5026
  32 141 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 141 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 141 207 3 10 47 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 141 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 29 141 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 207
  (Polychromatic418967fa.accept_16_12_13_15_1_1966 28 141 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 141 207 3 9 47 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 141 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 141 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 207
  (Polychromatic418967fa.accept_12_1_9_3_1_370 25 141 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 141 207 3 8 47 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 141 207 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 141 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 141 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 141 207 3 7 47 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 141 207
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 20 141 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 141 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 141 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 141 207 3 6 47 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 141 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 141 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 141 207 (Polychromatic418967fa.accept_10_6_1_7_1_342 16 141 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 141 207 3 5 47 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 141 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  141 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 207
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 141 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 141 207 3 4 47 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 141 207 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 141 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 141 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 141 207 3 3 47 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 141 207
  (Polychromatic418967fa.accept_17_8_5_3_1_2397 8 141 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 141 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 141 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 141 207 3 2 47 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 141 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 141 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 207
  (Polychromatic418967fa.accept_10_4_1_7_1_371 4 141 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 141 207 3 1 47 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 141 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 141 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 207 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 141 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 140 207 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 140 207 (accept_3_4 67 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 140 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 66 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 140 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 140 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 140 207 (accept_3_4 64 140 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 140 207 (Polychromatic418967fa.accept_13_11_10_12_1_1338 63 140 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 140 207
  (Polychromatic418967fa.accept_15_2_5_12_1_369 62 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 140 207 (accept_3_4 61 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 140 207 (Polychromatic418967fa.accept_13_8_10_12_1_1337 60 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 140 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 140 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 140 207 (accept_3_4 58 140 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 140 207 (Polychromatic418967fa.accept_18_3_14_9_1_4264 57 140 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 140 207
  (Polychromatic418967fa.accept_16_8_12_15_1_2005 56 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 140 207 (accept_3_4 55 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 140 207 (Polychromatic418967fa.accept_11_10_8_9_1_492 54 140 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 140 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 140 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 140 207 (accept_3_4 52 140 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 140 207 (Polychromatic418967fa.accept_8_3_4_7_1_475
  51 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 140 207
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 50 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 140 207 (accept_3_4 49 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 140 207 (Polychromatic418967fa.accept_13_9_10_12_1_2048 48 140 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 140 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 47
  140 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 140 207 (accept_3_4 46
  140 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 140 207
  (Polychromatic418967fa.accept_13_6_10_12_1_2049 45 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 140 207 (Polychromatic418967fa.accept_25_19_15_7_1_12096 44 140 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 140 207 (accept_3_4 43 140 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 140 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 140 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 140 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 140 207 (accept_3_4 40 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 140 207 (Polychromatic418967fa.accept_15_9_5_12_1_1640 39 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 140 207 (Polychromatic418967fa.accept_15_8_5_12_1_4453 38 140 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 140 207 (accept_3_4 37 140 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 140 207 (Polychromatic418967fa.accept_15_6_5_12_1_1642 36 140
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 140 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 140 207 (accept_3_4 34 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 140 207 (Polychromatic418967fa.accept_13_7_10_12_1_2047 33 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 140 207 (Polychromatic418967fa.accept_11_10_8_9_1_492 32 140 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 140 207 (accept_3_4 31 140 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 140 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 140 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 140 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 140 207 (accept_3_4 28 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 140 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 140 207 (Polychromatic418967fa.accept_21_5_14_18_1_4418 26 140 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 140 207 (accept_3_4 25 140 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 140 207 (Polychromatic418967fa.accept_13_11_10_12_1_1338 24
  140 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 140 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 140 207 (accept_3_4 22 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 140 207 (Polychromatic418967fa.accept_11_10_8_9_1_492 21 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 140 207 (Polychromatic418967fa.accept_13_7_10_12_1_2047 20 140 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 140 207 (accept_3_4 19 140 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 140 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 140 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 140 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 140 207 (accept_3_4 16 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 140 207 (Polychromatic418967fa.accept_13_2_10_12_1_757 15 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 140 207 (Polychromatic418967fa.accept_25_14_15_7_1_12118 14 140 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 140 207 (accept_3_4 13 140 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 140 207 (Polychromatic418967fa.accept_21_12_14_18_1_3005 12
  140 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 140 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 140 207 (accept_3_4 10 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  140 207 (Polychromatic418967fa.accept_13_9_10_12_1_2048 9 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 140 207 (Polychromatic418967fa.accept_13_8_10_12_1_1337 8 140 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 140 207 (accept_3_4 7 140 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 140 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 140 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 140 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 140 207 (accept_3_4 4 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  140 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 140 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 140 207 (Polychromatic418967fa.accept_13_2_10_12_1_757 2 140 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 140 207 (accept_3_4 1 140 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 140 207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 69 139 207 (Eq.refl Bool.true) (allA_succ_of_accept 68 139 207 (accept_3_5 68 139 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 139 207 (Polychromatic418967fa.accept_15_7_4_12_1_2530 67 139 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 139 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 66 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 139 207 (accept_3_5 65 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 139 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 139 207 (Polychromatic418967fa.accept_25_13_14_7_1_12117 63 139 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 139 207 (accept_3_5 62 139 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 139 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 139 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 139 207
  (Polychromatic418967fa.accept_8_4_3_7_1_491 60 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 139 207 (accept_3_5 59 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 139 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 139 207 (Polychromatic418967fa.accept_11_2_7_9_1_890 57 139 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 139 207 (accept_3_5 56 139 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 139 207 (Polychromatic418967fa.accept_13_3_9_12_1_2062 55 139
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 139 207
  (Polychromatic418967fa.accept_7_5_6_4_1_117 54 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 139 207 (accept_3_5 53 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 139 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 139 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 139 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 139 207 (accept_3_5 50 139 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 139 207 (Polychromatic418967fa.accept_11_5_7_9_1_2696 49 139 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 139 207
  (Polychromatic418967fa.accept_10_8_9_7_1_1118 48 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 139 207 (accept_3_5 47 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 139 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 139 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 139 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 139 207 (accept_3_5 44 139 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 139 207 (Polychromatic418967fa.accept_25_18_14_7_1_12116 43 139 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 139 207
  (Polychromatic418967fa.accept_10_2_9_7_1_720 42 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 139 207 (accept_3_5 41 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 139 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 139 207 (Polychromatic418967fa.accept_15_9_4_12_1_1611 39 139 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 139 207 (accept_3_5 38 139 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 139 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 139 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 139 207
  (Polychromatic418967fa.accept_8_4_3_7_1_491 36 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 139 207 (accept_3_5 35 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 139 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 139 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 139 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 139 207 (accept_3_5 32 139 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 139 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 139 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 139 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 139 207 (accept_3_5 29 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 139 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 139 207 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 139 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 139 207 (accept_3_5 26 139 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 139 207 (Polychromatic418967fa.accept_21_4_13_18_1_137 25 139
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 139 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 139 207 (accept_3_5 23 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 139 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 139 207 (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 139 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 139 207 (accept_3_5 20 139 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 139 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 139 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 139 207
  (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 139 207 (accept_3_5 17 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 139 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 139 207 (Polychromatic418967fa.accept_21_15_13_18_1_7523 15 139 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 139 207 (accept_3_5 14 139 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 139 207 (Polychromatic418967fa.accept_11_2_7_9_1_890 13 139
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 139 207
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 139 207 (accept_3_5 11 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 139 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 139 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 139 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 139 207 (accept_3_5 8 139 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 139 207 (Polychromatic418967fa.accept_15_7_4_12_1_2530 7 139 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 139 207
  (Polychromatic418967fa.accept_18_6_13_9_1_4218 6 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 139 207 (accept_3_5 5 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  139 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 139 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 139 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 139 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 139 207 (accept_3_5 2 139 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 139 207 (Polychromatic418967fa.accept_15_1_4_12_1_2401 1 139 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 139
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 138 207 (Eq.refl Bool.true)
  (allA_succ_of_gcd 69 138 207 69 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 138 207 (Polychromatic418967fa.accept_12_8_6_3_1_366 68 138 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 138 207 (Polychromatic418967fa.accept_15_7_3_12_1_365 67 138
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 138 207 3 22 46 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 138 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 138 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 138 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 138 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 138 207 3 21 46 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 138 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 62
  138 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 138 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 61 138 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 138 207 3 20 46 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 138 207 (Polychromatic418967fa.accept_10_9_8_7_1_714 59 138 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 138 207 (Polychromatic418967fa.accept_7_2_5_4_1_115
  58 138 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 138 207 3 19 46 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 138 207
  (Polychromatic418967fa.accept_12_8_6_3_1_366 56 138 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 138 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 138 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 138 207 3 18 46 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 138 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 53
  138 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 138 207
  (Polychromatic418967fa.accept_12_4_6_3_1_332 52 138 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 138 207 3 17 46 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 138 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 50 138 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 138 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 49
  138 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 138 207 3 16 46 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 138 207
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 47 138 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 138 207 23 2 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 138 207 3 15 46 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 138 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 138 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 138 207 (Polychromatic418967fa.accept_7_1_5_4_1_134
  43 138 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 138 207 3 14 46 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 138 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 138 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 138 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 138 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 138 207 3 13 46 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 138 207 (Polychromatic418967fa.accept_12_2_6_3_1_331
  38 138 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 138 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 138 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 207 3 12 46 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 207 (Polychromatic418967fa.accept_10_5_8_7_1_2174 35 138 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 138 207
  (Polychromatic418967fa.accept_7_6_5_4_1_297 34 138 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 138 207 3 11 46 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 138 207 (Polychromatic418967fa.accept_12_8_6_3_1_366 32 138 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 138 207
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 31 138 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 207 3 10 46 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 138 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 138 207 (Polychromatic418967fa.accept_12_4_6_3_1_332
  28 138 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 138 207 3 9 46 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 138 207
  (Polychromatic418967fa.accept_12_2_6_3_1_331 26 138 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 138 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 138 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 138 207 3 8 46 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 23 138 207 23 1 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 22 138 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 22
  138 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 138 207 3 7 46 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 138 207
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 138 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 138 207 (Polychromatic418967fa.accept_10_9_8_7_1_714 19 138 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 138 207 3 6 46 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 138 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 17
  138 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 138 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 16 138 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 138 207 3 5 46 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 138 207 (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 138 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 138 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 138 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 207 3 4 46 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 207
  (Polychromatic418967fa.accept_16_11_10_15_1_6301 11 138 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 138 207 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 138 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 138 207 3 3 46 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 138 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 138 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 138 207 (Polychromatic418967fa.accept_13_7_8_12_1_2810 7 138 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 207 3 2 46 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 138 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 138 207
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 138 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 138 207 3 1 46 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 138 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 138 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 138 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 138 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 137 207 (Eq.refl Bool.true)
  (allA_succ_of_accept 70 137 207 (accept_3_4 70 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 137 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 69 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 137 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 137 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 137 207 (accept_3_4 67 137 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 137 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 137 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 137 207
  (Polychromatic418967fa.accept_15_5_2_12_1_2543 65 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 137 207 (accept_3_4 64 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 137 207 (Polychromatic418967fa.accept_13_11_7_12_1_2758 63 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 137 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 137 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 137 207 (accept_3_4 61 137 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 137 207 (Polychromatic418967fa.accept_13_8_7_12_1_3637 60 137 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 137 207
  (Polychromatic418967fa.accept_15_14_2_12_1_2472 59 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 137 207 (accept_3_4 58 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 137 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 57 137 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 137 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 137 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 137 207 (accept_3_4 55 137 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 137 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 54
  137 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 137 207
  (Polychromatic418967fa.accept_17_2_1_3_1_2357 53 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 137 207 (accept_3_4 52 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 137 207 (Polychromatic418967fa.accept_11_7_5_9_1_884 51 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 137 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 137 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 137 207 (accept_3_4 49 137 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 137 207 (Polychromatic418967fa.accept_15_3_2_12_1_2469 48 137 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 137 207
  (Polychromatic418967fa.accept_13_8_7_12_1_3637 47 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 137 207 (accept_3_4 46 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 137 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 137 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 137 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 137 207 (accept_3_4 43 137 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 137 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 137 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 137 207
  (Polychromatic418967fa.accept_21_20_11_18_1_3037 41 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 137 207 (accept_3_4 40 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 137 207 (Polychromatic418967fa.accept_19_1_4_17_1_5136 39 137 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 137 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 137 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 137 207 (accept_3_4 37 137 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 137 207
  (Polychromatic418967fa.accept_13_10_7_12_1_2782 36 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 137 207 (Polychromatic418967fa.accept_15_5_2_12_1_2543 35 137 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 137 207 (accept_3_4 34 137 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 137 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 137
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 137 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 137 207 (accept_3_4 31 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 137 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 137 207 (Polychromatic418967fa.accept_11_7_5_9_1_884 29 137 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 207 (accept_3_4 28 137 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 137 207 (Polychromatic418967fa.accept_19_8_4_17_1_9510 27 137
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 137 207 (accept_3_4 25 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 137 207 (Polychromatic418967fa.accept_13_11_7_12_1_2758 24 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 137 207 (Polychromatic418967fa.accept_13_10_7_12_1_2782 23 137 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 207 (accept_3_4 22 137 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 137
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 207 (accept_3_4 19 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 137 207 (Polychromatic418967fa.accept_13_4_7_12_1_2823 17 137 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 207 (accept_3_4 16 137 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 207 (Polychromatic418967fa.accept_17_15_1_3_1_1488 15 137
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 137 207 (accept_3_4 13 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 137 207 (Polychromatic418967fa.accept_18_12_11_9_1_4257 12 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 207 (Polychromatic418967fa.accept_13_11_7_12_1_2758 11 137 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 207 (accept_3_4 10 137 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 137 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 207 (accept_3_4 7 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 207 (Polychromatic418967fa.accept_13_5_7_12_1_2757 5 137 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 207 (accept_3_4 4 137 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 207 (Polychromatic418967fa.accept_15_3_2_12_1_2469 3 137
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 207 (accept_3_4 1 137 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 136 207 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 136 207 (accept_3_5 71 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 136 207 (Polychromatic418967fa.accept_13_5_6_12_1_2750 70 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 136 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 136 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 136 207 (accept_3_5 68 136 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 136 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 136 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 136 207
  (Polychromatic418967fa.accept_12_6_4_3_1_361 66 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 136 207 (accept_3_5 65 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 136 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 136 207 (Polychromatic418967fa.accept_10_3_6_7_1_2188 63 136 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 136 207 (accept_3_5 62 136 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 136 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 136 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 136 207
  (Polychromatic418967fa.accept_16_12_8_15_1_5119 60 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 136 207 (accept_3_5 59 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 136 207 (Polychromatic418967fa.accept_15_13_1_12_1_1638 58 136 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 136 207 (Polychromatic418967fa.accept_7_1_3_4_1_128
  57 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 136 207 (accept_3_5 56
  136 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 136 207
  (Polychromatic418967fa.accept_6_1_4_3_1_14 55 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 136 207 (Polychromatic418967fa.accept_12_6_4_3_1_361 54 136 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 136 207 (accept_3_5 53 136 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 136 207 (Polychromatic418967fa.accept_16_4_8_15_1_1113 52 136 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 136 207
  (Polychromatic418967fa.accept_10_1_6_7_1_710 51 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 136 207 (accept_3_5 50 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 136 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 136 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 136 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 136 207 (accept_3_5 47 136 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 136 207 (Polychromatic418967fa.accept_11_2_4_9_1_484 46 136 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 136 207
  (Polychromatic418967fa.accept_21_3_10_18_1_7631 45 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 136 207 (accept_3_5 44 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 136 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 136 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 136 207 (Polychromatic418967fa.accept_12_6_4_3_1_361 42 136
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 136 207 (accept_3_5 41 136
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 136 207
  (Polychromatic418967fa.accept_19_2_3_17_1_5146 40 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 136 207 (Polychromatic418967fa.accept_16_7_8_15_1_6327 39 136 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 136 207 (accept_3_5 38 136 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 136 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 136 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 136 207 (Polychromatic418967fa.accept_7_1_3_4_1_128
  36 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 136 207 (accept_3_5 35
  136 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 136 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 34 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 136 207 (Polychromatic418967fa.accept_10_3_6_7_1_2188 33 136 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 136 207 (accept_3_5 32 136 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 136 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 136 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 136 207 (Polychromatic418967fa.accept_12_6_4_3_1_361
  30 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 136 207 (accept_3_5 29
  136 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 136 207
  (Polychromatic418967fa.accept_13_2_6_12_1_1334 28 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 136 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 136 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 136 207 (accept_3_5 26 136 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 136 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 136 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 136 207 (Polychromatic418967fa.accept_11_2_4_9_1_484
  24 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 136 207 (accept_3_5 23
  136 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 136 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 22 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 136 207 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 136 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 136 207 (accept_3_5 20 136 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 136 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 136 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 136 207 (Polychromatic418967fa.accept_12_6_4_3_1_361
  18 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 136 207 (accept_3_5 17
  136 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 136 207
  (Polychromatic418967fa.accept_19_16_3_17_1_6575 16 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 136 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 136 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 136 207 (accept_3_5 14 136 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 136 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 136 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 136 207
  (Polychromatic418967fa.accept_16_12_8_15_1_5119 12 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 136 207 (accept_3_5 11 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 136 207 (Polychromatic418967fa.accept_13_10_6_12_1_2780 10 136 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 136 207 (Polychromatic418967fa.accept_16_9_8_15_1_5095
  9 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 136 207 (accept_3_5 8
  136 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 136 207
  (Polychromatic418967fa.accept_6_1_4_3_1_14 7 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 136 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 136 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 136 207 (accept_3_5 5 136 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 136 207 (Polychromatic418967fa.accept_15_4_1_12_1_914 4 136 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 136 207 (Polychromatic418967fa.accept_10_3_6_7_1_2188
  3 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 136 207 (accept_3_5 2
  136 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 136 207
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 136 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 136 207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 135 207
  (Eq.refl Bool.true) (allA_succ_of_gcd 72 135 207 9 8 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 135 207 (Polychromatic418967fa.accept_13_6_5_12_1_307 71 135 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 135 207
  (Polychromatic418967fa.accept_16_6_7_15_1_1942 70 135 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 135 207 3 23 45 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 135 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 68 135 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 135 207
  (Polychromatic418967fa.accept_13_2_5_12_1_2043 67 135 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 135 207 3 22 45 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 135 207 (Polychromatic418967fa.accept_20_5_15_7_1_7869 65 135 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 135 207
  (Polychromatic418967fa.accept_17_13_16_3_1_1431 64 135 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 135 207 9 7 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 135 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 62 135 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 135 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 61 135 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 135 207 3 20 45 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 135 207 (Polychromatic418967fa.accept_13_7_5_12_1_1305 59 135 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 135 207
  (Polychromatic418967fa.accept_10_8_5_7_1_358 58 135 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 135 207 3 19 45 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 135 207 (Polychromatic418967fa.accept_13_4_5_12_1_751 56 135 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 135 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 55 135 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 135 207 9 6 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 135 207 (Polychromatic418967fa.accept_10_3_5_7_1_330 53 135 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 135 207 (Polychromatic418967fa.accept_10_2_5_7_1_1124 52 135
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 135 207 3 17 45 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 135 207
  (Polychromatic418967fa.accept_11_6_3_9_1_906 50 135 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 135 207 (Polychromatic418967fa.accept_21_7_9_18_1_7519 49 135 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 135 207 3 16 45 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 135 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 47
  135 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 207
  (Polychromatic418967fa.accept_13_7_5_12_1_1305 46 135 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 135 207 9 5 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 135 207 (Polychromatic418967fa.accept_14_2_9_11_1_3054 44 135 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 207 (Polychromatic418967fa.accept_10_3_5_7_1_330 43 135
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 135 207 3 14 45 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 135 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 135 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 135 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 135 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 135 207 3 13 45 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 135 207 (Polychromatic418967fa.accept_10_8_5_7_1_358
  38 135 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 207
  (Polychromatic418967fa.accept_22_15_3_9_1_9061 37 135 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 135 207 9 4 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 135 207 (Polychromatic418967fa.accept_16_3_7_15_1_1130 35 135 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 135 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 135 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 135 207 3 11 45 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 135 207
  (Polychromatic418967fa.accept_10_2_5_7_1_1124 32 135 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 135 207 (Polychromatic418967fa.accept_19_12_2_17_1_5210 31 135 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 135 207 3 10 45 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 135 207
  (Polychromatic418967fa.accept_19_10_2_17_1_675 29 135 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 135 207 (Polychromatic418967fa.accept_10_8_5_7_1_358 28 135 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 135 207 9 3 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 135 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 26
  135 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 207
  (Polychromatic418967fa.accept_20_5_15_7_1_7869 25 135 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 135 207 3 8 45 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 135 207 (Polychromatic418967fa.accept_10_3_5_7_1_330 23 135 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 207 (Polychromatic418967fa.accept_10_2_5_7_1_1124 22 135
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 135 207 3 7 45 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 135 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 135 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 135 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 135 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 135 207 9 2 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 135 207 (Polychromatic418967fa.accept_11_6_3_9_1_906
  17 135 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 207
  (Polychromatic418967fa.accept_14_2_9_11_1_3054 16 135 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 135 207 3 5 45 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 135 207 (Polychromatic418967fa.accept_13_1_5_12_1_306 14 135 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 135 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 135 207 3 4 45 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 135 207
  (Polychromatic418967fa.accept_16_11_7_15_1_1998 11 135 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 135 207 (Polychromatic418967fa.accept_19_10_2_17_1_675 10 135 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 135 207 9 1 15 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 135 207
  (Polychromatic418967fa.accept_10_8_5_7_1_358 8 135 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 135 207 (Polychromatic418967fa.accept_13_7_5_12_1_1305 7 135 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 135 207 3 2 45 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 135 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 135 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 207
  (Polychromatic418967fa.accept_13_4_5_12_1_751 4 135 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 135 207 3 1 45 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 135 207 (Polychromatic418967fa.accept_10_2_5_7_1_1124 2 135 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 207 (Polychromatic418967fa.accept_13_1_5_12_1_306 1 135 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 134 207 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 134 207 (accept_3_4 73 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 134 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 72 134 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 134 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 134 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 134 207 (accept_3_4 70 134 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 134 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 69
  134 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 134 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 68 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 134 207 (accept_3_4 67 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 134 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 134 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 134 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 134 207 (accept_3_4 64 134 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 134 207 (Polychromatic418967fa.accept_10_3_4_7_1_353 63 134 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 134 207
  (Polychromatic418967fa.accept_10_2_4_7_1_352 62 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 134 207 (accept_3_4 61 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 134 207 (Polychromatic418967fa.accept_13_8_4_12_1_2753 60 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 134 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 134 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 134 207 (accept_3_4 58 134 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 134 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 134 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 134 207
  (Polychromatic418967fa.accept_15_11_14_12_1_2458 56 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 134 207 (accept_3_4 55 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 134 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 134 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 134 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 134 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 134 207 (accept_3_4 52 134 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 134 207 (Polychromatic418967fa.accept_10_1_4_7_1_374
  51 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 134 207
  (Polychromatic418967fa.accept_13_11_4_12_1_3585 50 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 134 207 (accept_3_4 49 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 134 207 (Polychromatic418967fa.accept_11_4_2_9_1_496 48 134 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 134 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 134 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 134 207 (accept_3_4 46 134 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 134 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 45
  134 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 134 207
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 44 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 134 207 (accept_3_4 43 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 134 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 134 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 134 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 134 207 (accept_3_4 40 134 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 134 207 (Polychromatic418967fa.accept_15_9_14_12_1_913 39 134 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 134 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 134 207 (accept_3_4 37 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 134 207 (Polychromatic418967fa.accept_21_15_8_18_1_10689 36 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 134 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 134 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 134 207 (accept_3_4 34 134 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 134 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 134 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 134 207
  (Polychromatic418967fa.accept_10_2_4_7_1_352 32 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 134 207 (accept_3_4 31 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 134 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 134 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 134 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 134 207 (accept_3_4 28 134 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 134 207 (Polychromatic418967fa.accept_24_3_14_15_1_12115 27 134 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 134 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 134 207 (accept_3_4 25 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 134 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 134 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 134 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 134 207 (accept_3_4 22 134 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 134 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 134 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 134 207
  (Polychromatic418967fa.accept_13_7_4_12_1_1341 20 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 134 207 (accept_3_4 19 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 134 207 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 134 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 134 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 134 207 (accept_3_4 16 134 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 134 207 (Polychromatic418967fa.accept_11_4_2_9_1_496 15 134 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 134 207
  (Polychromatic418967fa.accept_17_14_15_3_1_4618 14 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 134 207 (accept_3_4 13 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 134 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 134 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 134 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 134 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 134 207 (accept_3_4 10 134 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 134 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9
  134 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 134 207
  (Polychromatic418967fa.accept_13_8_4_12_1_2753 8 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 134 207 (accept_3_4 7 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  134 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 134 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 134 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 134 207 (accept_3_4 4 134 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 134 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 134 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 134 207
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 134 207 (accept_3_4 1 134 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 133 207 (Eq.refl
  Bool.true) (allA_succ_of_accept 74 133 207 (accept_3_5 74 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 133 207 (Polychromatic418967fa.accept_14_3_7_11_1_765 73 133 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 133 207 (Polychromatic418967fa.accept_21_9_7_18_1_1780 72 133
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 133 207 (accept_3_5 71 133
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 133 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 70 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 133 207 (Polychromatic418967fa.accept_12_9_1_3_1_350 69 133 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 133 207 (accept_3_5 68 133 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 133 207 (Polychromatic418967fa.accept_13_2_3_12_1_735 67 133 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 133 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 133 207 (accept_3_5 65 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 133 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 133 207 (Polychromatic418967fa.accept_15_3_13_12_1_348 63 133 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 133 207 (accept_3_5 62 133 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 133 207 (Polychromatic418967fa.accept_13_9_3_12_1_2025 61 133
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 133 207
  (Polychromatic418967fa.accept_14_4_7_11_1_790 60 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 133 207 (accept_3_5 59 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 133 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 133 207 (Polychromatic418967fa.accept_12_9_1_3_1_350 57 133 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 133 207 (accept_3_5 56 133 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 133 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 55 133
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 133 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 133 207 (accept_3_5 53 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 133 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 133 207 (Polychromatic418967fa.accept_21_9_7_18_1_1780 51 133 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 133 207 (accept_3_5 50 133 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 133 207 (Polychromatic418967fa.accept_16_1_5_15_1_2918 49 133
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 133 207
  (Polychromatic418967fa.accept_13_9_3_12_1_2025 48 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 133 207 (accept_3_5 47 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 133 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 133 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 133 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 133 207 (accept_3_5 44 133 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 133 207 (Polychromatic418967fa.accept_11_10_1_9_1_2060 43 133
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 133 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 133 207 (accept_3_5 41 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 133 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 133 207 (Polychromatic418967fa.accept_18_3_7_9_1_5486 39 133 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 133 207 (accept_3_5 38 133 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 133 207 (Polychromatic418967fa.accept_22_15_1_9_1_12114 37 133
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 133 207
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 133 207 (accept_3_5 35 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 133 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 133 207 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 133 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 133 207 (accept_3_5 32 133 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 133 207 (Polychromatic418967fa.accept_14_3_7_11_1_765 31 133
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 133 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 133 207 (accept_3_5 29 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 133 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 133 207 (Polychromatic418967fa.accept_21_6_7_18_1_1783 27 133 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 133 207 (accept_3_5 26 133 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 133 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 133
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 133 207
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 133 207 (accept_3_5 23 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 133 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 133 207 (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 133 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 133 207 (accept_3_5 20 133 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 133 207 (Polychromatic418967fa.accept_17_2_14_3_1_4679 19 133
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 133 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 133 207 (accept_3_5 17 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 133 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 133 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 133 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 133 207 (accept_3_5 14 133 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 133 207 (Polychromatic418967fa.accept_21_13_7_18_1_5966 13 133
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 207
  (Polychromatic418967fa.accept_21_12_7_18_1_7683 12 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 133 207 (accept_3_5 11 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 133 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 133 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 207 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 133 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 207 (accept_3_5 8 133 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 133 207
  (Polychromatic418967fa.accept_24_7_13_15_1_12081 7 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 133 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 133 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 207 (accept_3_5 5 133 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 133 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 207
  (Polychromatic418967fa.accept_14_3_7_11_1_765 3 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 207 (accept_3_5 2 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 207 (Polychromatic418967fa.accept_15_1_13_12_1_347 1 133 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133 207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  76 132 207 (Eq.refl Bool.true) (allA_succ_of_gcd 75 132 207 3 25 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 132 207 (Polychromatic418967fa.accept_10_4_2_7_1_373
  74 132 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 132 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 73 132 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 132 207 3 24 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 132 207 (Polychromatic418967fa.accept_13_6_2_12_1_2802 71 132 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 132 207
  (Polychromatic418967fa.accept_13_5_2_12_1_1301 70 132 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 132 207 3 23 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 132 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 68 132 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 132 207 (Polychromatic418967fa.accept_8_3_4_7_1_475
  67 132 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 132 207 3 22 44 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 132 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 65 132 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 132 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 64 132 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 132 207 3 21 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 132 207
  (Polychromatic418967fa.accept_13_10_2_12_1_1332 62 132 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 132 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 132 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 132 207 3 20 44 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 132 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 132 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 132 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 132 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 132 207 3 19 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 132 207 (Polychromatic418967fa.accept_13_4_2_12_1_2800
  56 132 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 132 207
  (Polychromatic418967fa.accept_10_5_2_7_1_345 55 132 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 132 207 3 18 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 132 207 (Polychromatic418967fa.accept_13_1_2_12_1_1299 53 132 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 132 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 52 132 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 132 207 3 17 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 132 207 (Polychromatic418967fa.accept_17_16_13_3_1_4677 50 132 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 132 207
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 49 132 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 132 207 3 16 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 132 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 132 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 132 207
  (Polychromatic418967fa.accept_16_14_4_15_1_3944 46 132 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 132 207 3 15 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 132 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 132 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 132 207
  (Polychromatic418967fa.accept_8_3_4_7_1_475 43 132 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 132 207 3 14 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 132 207 (Polychromatic418967fa.accept_21_20_6_18_1_7709 41 132 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 132 207
  (Polychromatic418967fa.accept_7_5_6_4_1_117 40 132 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 132 207 3 13 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 132 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 132 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 132 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 37
  132 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 132 207 3 12 44 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 132 207
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 132 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 132 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 34 132 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 132 207 3 11 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 132 207 (Polychromatic418967fa.accept_13_6_2_12_1_2802
  32 132 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 132 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 132 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 132 207 3 10 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 132 207 (Polychromatic418967fa.accept_10_9_2_7_1_1096 29 132 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 132 207
  (Polychromatic418967fa.accept_16_12_4_15_1_5091 28 132 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 132 207 3 9 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 132 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 132 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 132 207
  (Polychromatic418967fa.accept_10_5_2_7_1_345 25 132 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 207 3 8 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 132 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 132 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 132 207 (Polychromatic418967fa.accept_20_2_12_7_1_4799 22 132
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 132 207 3 7 44 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 132 207
  (Polychromatic418967fa.accept_18_2_6_9_1_1032 20 132 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 132 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 132 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 132 207 3 6 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 132 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 17
  132 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 132 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 16 132 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 132 207 3 5 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 132 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 132 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 132 207 (Polychromatic418967fa.accept_18_13_6_9_1_4280 13 132
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 207 3 4 44 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 132 207
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 132 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 132 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 132 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 132 207 3 3 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 132 207 (Polychromatic418967fa.accept_16_8_4_15_1_2941 8 132 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 132 207
  (Polychromatic418967fa.accept_18_7_6_9_1_4205 7 132 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 132 207 3 2 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 132 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 132 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 132 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 132 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 132 207 3 1 44 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 132 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 132 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 132 207 (Polychromatic418967fa.accept_13_1_2_12_1_1299 1 132 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 132
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 131 207 (Eq.refl
  Bool.true) (allA_succ_of_accept 76 131 207 (accept_3_4 76 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 131 207 (Polychromatic418967fa.accept_16_11_3_15_1_1989 75 131 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 131 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 74
  131 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 131 207 (accept_3_4 73
  131 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 131 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 72 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 131 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 71 131 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 131 207 (accept_3_4 70 131 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 131 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 131 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 131 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 68
  131 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 131 207 (accept_3_4 67
  131 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 131 207
  (Polychromatic418967fa.accept_10_6_1_7_1_342 66 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 131 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 65 131 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 131 207 (accept_3_4 64 131 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 131 207 (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 131 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 131 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 62 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 131 207 (accept_3_4 61 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 131 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 131 207 (Polychromatic418967fa.accept_15_14_11_12_1_4440 59 131 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 131 207 (accept_3_4 58 131 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 131 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 131 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 131 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 131 207 (accept_3_4 55 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 131 207 (Polychromatic418967fa.accept_10_4_1_7_1_371 54 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 131 207 (Polychromatic418967fa.accept_15_8_11_12_1_1626 53 131 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 131 207 (accept_3_4 52 131 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 131 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 131 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 131 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 131 207 (accept_3_4 49 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 131 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 131 207 (Polychromatic418967fa.accept_13_8_1_12_1_762 47 131 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 131 207 (accept_3_4 46 131 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 131 207 (Polychromatic418967fa.accept_11_1_10_9_1_871 45 131
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 131 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 131 207 (accept_3_4 43 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 131 207 (Polychromatic418967fa.accept_17_8_12_3_1_5927 42 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 131 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 131 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 131 207 (accept_3_4 40 131 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 131 207 (Polychromatic418967fa.accept_16_7_3_15_1_2940 39 131 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 131 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 131 207 (accept_3_4 37 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 131 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 131 207 (Polychromatic418967fa.accept_21_14_5_18_1_7618 35 131 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 131 207 (accept_3_4 34 131 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 131 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 131
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 131 207 (accept_3_4 31 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 131 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 131 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 131 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 207 (accept_3_4 28 131 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 131 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 131 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 131 207 (accept_3_4 25 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 131 207 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 131 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 131 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 207 (accept_3_4 22 131 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 131 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 131 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 131 207 (accept_3_4 19 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 207 (Polychromatic418967fa.accept_13_5_1_12_1_740 18 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 131 207 (Polychromatic418967fa.accept_25_17_6_7_1_12113 17 131 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 207 (accept_3_4 16 131 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 131 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 131 207 (accept_3_4 13 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 131 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 131 207 (Polychromatic418967fa.accept_13_11_1_12_1_742 11 131 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 207 (accept_3_4 10 131 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 131 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 207 (accept_3_4 7 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 207 (Polychromatic418967fa.accept_13_5_1_12_1_740 5 131 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 207 (accept_3_4 4 131 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 207 (Polychromatic418967fa.accept_21_3_5_18_1_7512 3 131 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 207 (accept_3_4 1 131 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 130 207 (Eq.refl
  Bool.true) (allA_succ_of_accept 77 130 207 (accept_3_5 77 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 130 207 (Polychromatic418967fa.accept_16_12_2_15_1_490 76 130 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 130 207 (Polychromatic418967fa.accept_19_18_16_17_1_2626 75
  130 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 130 207 (accept_3_5 74
  130 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 130 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 73 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 130 207 (Polychromatic418967fa.accept_21_9_4_18_1_7615 72 130 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 130 207 (accept_3_5 71 130 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 130 207 (Polychromatic418967fa.accept_17_2_11_3_1_4654 70 130 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 130 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 130 207 (accept_3_5 68 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 130 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 130 207 (Polychromatic418967fa.accept_12_6_10_3_1_1313 66 130 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 130 207 (accept_3_5 65 130 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 130 207 (Polychromatic418967fa.accept_14_8_4_11_1_3035 64 130
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 130 207
  (Polychromatic418967fa.accept_14_7_4_11_1_3038 63 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 130 207 (accept_3_5 62 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 130 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 130 207 (Polychromatic418967fa.accept_16_12_2_15_1_490 60 130 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 130 207 (accept_3_5 59 130 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 130 207 (Polychromatic418967fa.accept_15_13_10_12_1_2503 58
  130 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 130 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 130 207 (accept_3_5 56 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 130 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 130 207 (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 130 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 130 207 (accept_3_5 53 130 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 130 207 (Polychromatic418967fa.accept_15_7_10_12_1_2403 52 130
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 130 207
  (Polychromatic418967fa.accept_15_6_10_12_1_2538 51 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 130 207 (accept_3_5 50 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 130 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 130 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 130 207 (Polychromatic418967fa.accept_17_14_11_3_1_4653 48 130
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 130 207 (accept_3_5 47 130
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 130 207
  (Polychromatic418967fa.accept_19_8_16_17_1_6552 46 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 130 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 130 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 130 207 (accept_3_5 44 130 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 130 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 130 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 130 207
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 130 207 (accept_3_5 41 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 130 207 (Polychromatic418967fa.accept_19_2_16_17_1_12112 40 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 130 207 (Polychromatic418967fa.accept_15_9_10_12_1_1625 39 130 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 130 207 (accept_3_5 38 130 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 130 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 37
  130 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 130 207
  (Polychromatic418967fa.accept_14_8_4_11_1_3035 36 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 130 207 (accept_3_5 35 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 130 207 (Polychromatic418967fa.accept_21_13_4_18_1_7553 34 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 130 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 130 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 130 207 (accept_3_5 32 130 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 130 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 130 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 130 207
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 130 207 (accept_3_5 29 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 130 207 (Polychromatic418967fa.accept_15_13_10_12_1_2503 28 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 130 207 (Polychromatic418967fa.accept_17_10_11_3_1_3442 27 130 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 130 207 (accept_3_5 26 130 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 130 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 25
  130 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 130 207
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 24 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 130 207 (accept_3_5 23 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 130 207 (Polychromatic418967fa.accept_14_8_4_11_1_3035 22 130 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 130 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 130 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 130 207 (accept_3_5 20 130 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 130 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19
  130 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 130 207
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 130 207 (accept_3_5 17 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 130 207 (Polychromatic418967fa.accept_24_16_10_15_1_12111 16 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 130 207 (Polychromatic418967fa.accept_14_1_4_11_1_3036 15 130 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 130 207 (accept_3_5 14 130 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 130 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 13
  130 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 130 207
  (Polychromatic418967fa.accept_16_12_2_15_1_490 12 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 130 207 (accept_3_5 11 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 130 207 (Polychromatic418967fa.accept_17_10_11_3_1_3442 10 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 130 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 130 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 130 207 (accept_3_5 8 130 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 130 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 130 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 130 207
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 130 207 (accept_3_5 5 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  130 207 (Polychromatic418967fa.accept_22_4_20_9_1_12110 4 130 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 130 207 (Polychromatic418967fa.accept_16_3_2_15_1_7367 3 130 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 130 207 (accept_3_5 2 130 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 130 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 130 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 129 207 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 129 207 3 26 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 129 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 77 129 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 129 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 76 129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 129 207 3 25 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 129 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 129 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 129 207 (Polychromatic418967fa.accept_12_1_9_3_1_370
  73 129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 129 207 3 24 43 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 129 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 71 129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 129 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 129 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 129 207 3 23 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 129 207 (Polychromatic418967fa.accept_10_8_9_7_1_1118
  68 129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 129 207
  (Polychromatic418967fa.accept_12_7_9_3_1_767 67 129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 129 207 3 22 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 129 207 (Polychromatic418967fa.accept_11_10_8_9_1_492 65 129 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 129 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 64 129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 129 207 3 21 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 129 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 129 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 129 207 (Polychromatic418967fa.accept_12_1_9_3_1_370
  61 129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 129 207 3 20 43 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 129 207
  (Polychromatic418967fa.accept_12_11_9_3_1_792 59 129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 129 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 129 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 129 207 3 19 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 129 207 (Polychromatic418967fa.accept_16_8_1_15_1_1982
  56 129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 55 129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 129 207 3 18 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 129 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 53 129 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 129 207 (Polychromatic418967fa.accept_10_2_9_7_1_720
  52 129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 129 207 3 17 43 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 129 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 129 207 (Polychromatic418967fa.accept_12_1_9_3_1_370 49 129 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 129 207 3 16 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 129 207 (Polychromatic418967fa.accept_12_11_9_3_1_792
  47 129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 129 207 3 15 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 129 207 (Polychromatic418967fa.accept_15_14_9_12_1_2498 44 129 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 129 207 3 14 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 129 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 129 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 207
  (Polychromatic418967fa.accept_15_10_9_12_1_2497 40 129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 129 207 3 13 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 129 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 129 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 207
  (Polychromatic418967fa.accept_12_1_9_3_1_370 37 129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 129 207 3 12 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 129 207 (Polychromatic418967fa.accept_12_11_9_3_1_792 35 129 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 129 207 3 11 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 129 207 (Polychromatic418967fa.accept_10_2_9_7_1_720 32 129 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 207 (Polychromatic418967fa.accept_12_7_9_3_1_767
  31 129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 129 207 3 10 43 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 129 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 129 207 (Polychromatic418967fa.accept_10_8_9_7_1_1118 28 129 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 129 207 3 9 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 129 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 207
  (Polychromatic418967fa.accept_12_1_9_3_1_370 25 129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 129 207 3 8 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 129 207 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 129 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 129 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 129 207 3 7 43 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 129 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 129 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 129 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 129 207 3 6 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 129 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 17
  129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 207
  (Polychromatic418967fa.accept_20_16_9_7_1_3402 16 129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 129 207 3 5 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 129 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 129 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 129 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 129 207 3 4 43 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 129 207
  (Polychromatic418967fa.accept_12_11_9_3_1_792 11 129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 129 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 129 207 3 3 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 129 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 129 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 207
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 129 207 3 2 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 129 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 129 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 207 (Polychromatic418967fa.accept_15_4_9_12_1_2495 4 129
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 129 207 3 1 43 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 129 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 129 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 129 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 129 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 129
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 128 207 (Eq.refl
  Bool.true) (allA_succ_of_accept 79 128 207 (accept_3_4 79 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 128 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 78 128 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 128 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 128 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 128 207 (accept_3_4 76 128 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 128 207 (Polychromatic418967fa.accept_7_5_2_4_1_126
  75 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 128 207
  (Polychromatic418967fa.accept_17_6_9_3_1_704 74 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 128 207 (accept_3_4 73 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 128 207 (Polychromatic418967fa.accept_13_7_11_12_1_2051 72 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 128 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 128 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 128 207 (accept_3_4 70 128 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 128 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 128 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 128 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 68 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 128 207 (accept_3_4 67 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 128 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 66 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 128 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 128 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 128 207 (accept_3_4 64 128 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 128 207 (Polychromatic418967fa.accept_15_3_8_12_1_900 63 128 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 128 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 62 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 128 207 (accept_3_4 61 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 128 207 (Polychromatic418967fa.accept_11_5_7_9_1_2696 60 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 128 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 128 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 128 207 (accept_3_4 58 128 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 128 207 (Polychromatic418967fa.accept_11_2_7_9_1_890 57 128 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 128 207
  (Polychromatic418967fa.accept_13_4_11_12_1_1318 56 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 128 207 (accept_3_4 55 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 128 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 128 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 128 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 128 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 128 207 (accept_3_4 52 128 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 128 207 (Polychromatic418967fa.accept_14_9_2_11_1_780
  51 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 128 207
  (Polychromatic418967fa.accept_15_5_8_12_1_2435 50 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 128 207 (accept_3_4 49 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 128 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 128 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 128 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 128 207 (accept_3_4 46 128 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 128 207 (Polychromatic418967fa.accept_10_5_8_7_1_2174 45 128 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 128 207
  (Polychromatic418967fa.accept_17_10_9_3_1_7144 44 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 128 207 (accept_3_4 43 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 128 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 128 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 128 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 128 207 (accept_3_4 40 128 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 128 207 (Polychromatic418967fa.accept_10_9_8_7_1_714 39 128 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 128 207
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 38 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 128 207 (accept_3_4 37 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 128 207 (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 128 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 128 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 128 207 (accept_3_4 34 128 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 128 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 128 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 128 207
  (Polychromatic418967fa.accept_22_10_18_9_1_5685 32 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 128 207 (accept_3_4 31 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 128 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 128 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 128 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 128 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 128 207 (accept_3_4 28 128 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 128 207 (Polychromatic418967fa.accept_7_6_2_4_1_291
  27 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 128 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 128 207 (accept_3_4 25 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 128 207 (Polychromatic418967fa.accept_11_2_7_9_1_890 24 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 128 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 128 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 128 207 (accept_3_4 22 128 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 128 207 (Polychromatic418967fa.accept_18_3_2_9_1_1013 21 128 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 128 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 128 207 (accept_3_4 19 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 128 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 128 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 128 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 128 207 (accept_3_4 16 128 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 128 207 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 128 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 128 207
  (Polychromatic418967fa.accept_13_1_11_12_1_1322 14 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 128 207 (accept_3_4 13 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 128 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 128 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 128 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 128 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 128 207 (accept_3_4 10 128 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 128 207 (Polychromatic418967fa.accept_10_9_8_7_1_714 9
  128 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 128 207
  (Polychromatic418967fa.accept_22_8_18_9_1_5631 8 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 128 207 (accept_3_4 7 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  128 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 128 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 128 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 128 207 (accept_3_4 4 128 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 128 207 (Polychromatic418967fa.accept_15_3_8_12_1_900 3 128 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 128 207
  (Polychromatic418967fa.accept_11_2_7_9_1_890 2 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 128 207 (accept_3_4 1 128 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 127 207 (Eq.refl
  Bool.true) (allA_succ_of_accept 80 127 207 (accept_3_5 80 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 127 207 (Polychromatic418967fa.accept_15_4_7_12_1_5538 79 127 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 127 207 (Polychromatic418967fa.accept_15_3_7_12_1_372 78 127
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 127 207 (accept_3_5 77 127
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 127 207
  (Polychromatic418967fa.accept_6_4_1_3_1_77 76 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 127 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 127 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 127 207 (accept_3_5 74 127 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 127 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 73 127 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 127 207
  (Polychromatic418967fa.accept_13_7_10_12_1_2047 72 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 127 207 (accept_3_5 71 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 127 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 127 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 127 207 (Polychromatic418967fa.accept_11_3_6_9_1_1378 69 127
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 127 207 (accept_3_5 68 127
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 127 207
  (Polychromatic418967fa.accept_13_2_10_12_1_757 67 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 127 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 127 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 127 207 (accept_3_5 65 127 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 127 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 127 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 127 207
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 63 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 127 207 (accept_3_5 62 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 127 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 61 127 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 127 207 (Polychromatic418967fa.accept_13_8_10_12_1_1337 60 127
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 127 207 (accept_3_5 59 127
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 127 207
  (Polychromatic418967fa.accept_6_4_1_3_1_77 58 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 127 207 (Polychromatic418967fa.accept_12_9_7_3_1_1309 57 127 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 127 207 (accept_3_5 56 127 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 127 207 (Polychromatic418967fa.accept_15_10_7_12_1_2490 55 127 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 127 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 54 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 127 207 (accept_3_5 53 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 127 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 127 207 (Polychromatic418967fa.accept_15_6_7_12_1_869 51 127 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 127 207 (accept_3_5 50 127 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 127 207 (Polychromatic418967fa.accept_15_4_7_12_1_5538 49 127
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 127 207
  (Polychromatic418967fa.accept_13_9_10_12_1_2048 48 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 127 207 (accept_3_5 47 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 127 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 127 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 127 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 127 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 127 207 (accept_3_5 44 127 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 127 207
  (Polychromatic418967fa.accept_24_19_7_15_1_12109 43 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 127 207 (Polychromatic418967fa.accept_18_6_1_9_1_5551 42 127 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 127 207 (accept_3_5 41 127 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 127 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 127 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 127 207
  (Polychromatic418967fa.accept_17_5_8_3_1_1419 39 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 127 207 (accept_3_5 38 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 127 207 (Polychromatic418967fa.accept_13_11_10_12_1_1338 37 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 127 207 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 127 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 127 207 (accept_3_5 35 127 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 127 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 127 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 127 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 127 207 (accept_3_5 32 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 127 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 127 207 (Polychromatic418967fa.accept_17_13_8_3_1_7177 30 127 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 127 207 (accept_3_5 29 127 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 127 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 127 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 127 207
  (Polychromatic418967fa.accept_28_27_15_11_1_12108 27 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 127 207 (accept_3_5 26 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 127 207 (Polychromatic418967fa.accept_11_3_6_9_1_1378 25 127 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 127 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 127 207 (accept_3_5 23 127 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 127 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 22
  127 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 127 207
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 127 207 (accept_3_5 20 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 127 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 127 207 (Polychromatic418967fa.accept_14_4_1_11_1_5026 18 127 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 127 207 (accept_3_5 17 127 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 127 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 127 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 207
  (Polychromatic418967fa.accept_13_2_10_12_1_757 15 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 127 207 (accept_3_5 14 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 127 207 (Polychromatic418967fa.accept_17_13_8_3_1_7177 13 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 127 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 127 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 207 (accept_3_5 11 127 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 127 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 127 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 207
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 127 207 (accept_3_5 8 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  127 207 (Polychromatic418967fa.accept_13_7_10_12_1_2047 7 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 127 207 (Polychromatic418967fa.accept_13_6_10_12_1_2049 6 127 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 207 (accept_3_5 5 127 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 127 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 207 (accept_3_5 2 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 207 (Polychromatic418967fa.accept_25_1_2_7_1_12107 1 127 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127 207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 82 126 207 (Eq.refl Bool.true) (allA_succ_of_gcd 81 126 207 9 9 14 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 126 207
  (Polychromatic418967fa.accept_12_8_6_3_1_366 80 126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 126 207 (Polychromatic418967fa.accept_19_3_12_17_1_6585 79 126 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 126 207 3 26 42 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 126 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 126 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 76 126 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 126 207 3 25 42 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 126 207 (Polychromatic418967fa.accept_12_2_6_3_1_331
  74 126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 126 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 73 126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 126 207 9 8 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 126 207 (Polychromatic418967fa.accept_10_1_6_7_1_710 71 126 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 126 207 (Polychromatic418967fa.accept_12_10_6_3_1_786 70 126
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 126 207 3 23 42 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 126 207
  (Polychromatic418967fa.accept_12_8_6_3_1_366 68 126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 126 207 (Polychromatic418967fa.accept_15_7_6_12_1_1614 67 126 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 126 207 3 22 42 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 126 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 65
  126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 126 207
  (Polychromatic418967fa.accept_12_4_6_3_1_332 64 126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 126 207 9 7 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 126 207 (Polychromatic418967fa.accept_11_7_5_9_1_884 62 126 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 126 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 126 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 126 207 3 20 42 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 126 207
  (Polychromatic418967fa.accept_19_2_12_17_1_5197 59 126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 126 207 (Polychromatic418967fa.accept_12_10_6_3_1_786 58 126 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 126 207 3 19 42 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 126 207
  (Polychromatic418967fa.accept_12_8_6_3_1_366 56 126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 126 207 (Polychromatic418967fa.accept_13_3_9_12_1_2062 55 126 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 126 207 9 6 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 126 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 53
  126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 126 207
  (Polychromatic418967fa.accept_12_4_6_3_1_332 52 126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 126 207 3 17 42 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 126 207 (Polychromatic418967fa.accept_12_2_6_3_1_331 50 126 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 126 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 49
  126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 126 207 3 16 42 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 126 207
  (Polychromatic418967fa.accept_13_8_9_12_1_2813 47 126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 126 207 (Polychromatic418967fa.accept_12_10_6_3_1_786 46 126 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 126 207 9 5 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 126 207 (Polychromatic418967fa.accept_12_8_6_3_1_366
  44 126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 126 207
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 43 126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 126 207 3 14 42 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 126 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 126 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 126 207 (Polychromatic418967fa.accept_11_7_5_9_1_884
  40 126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 126 207 3 13 42 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 126 207
  (Polychromatic418967fa.accept_12_2_6_3_1_331 38 126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 126 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 126 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 126 207 9 4 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 126 207 (Polychromatic418967fa.accept_15_5_6_12_1_916
  35 126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 126 207
  (Polychromatic418967fa.accept_12_10_6_3_1_786 34 126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 126 207 3 11 42 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 126 207 (Polychromatic418967fa.accept_12_8_6_3_1_366 32 126 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 126 207 (Polychromatic418967fa.accept_10_1_6_7_1_710
  31 126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 126 207 3 10 42 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 126 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 126 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 126 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 126 207 9 3 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 126 207 (Polychromatic418967fa.accept_12_2_6_3_1_331
  26 126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 126 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 207 3 8 42 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 126 207 (Polychromatic418967fa.accept_10_3_6_7_1_2188 23 126 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 126 207 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 126
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 126 207 3 7 42 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 126 207
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 126 207 (Polychromatic418967fa.accept_20_19_6_7_1_9289 19 126 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 126 207 9 2 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 126 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 17
  126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 126 207
  (Polychromatic418967fa.accept_12_4_6_3_1_332 16 126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 126 207 3 5 42 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 126 207 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 126 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 126 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 126 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 207 3 4 42 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 207
  (Polychromatic418967fa.accept_10_1_6_7_1_710 11 126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 126 207 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 126 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 126 207 9 1 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 126 207 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 126 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 126 207
  (Polychromatic418967fa.accept_11_7_5_9_1_884 7 126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 126 207 3 2 42 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 126 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 126 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 126 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 126 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 126 207 3 1 42 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 126 207
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 126 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 126 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 126 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 126
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 125 207 (Eq.refl
  Bool.true) (allA_succ_of_accept 82 125 207 (accept_3_4 82 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 125 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 81 125 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 125 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 125 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 125 207 (accept_3_4 79 125 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 125 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 78
  125 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 125 207
  (Polychromatic418967fa.accept_15_2_5_12_1_369 77 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 125 207 (accept_3_4 76 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 125 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 125 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 125 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 125 207 (accept_3_4 73 125 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 125 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 125 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 125 207
  (Polychromatic418967fa.accept_19_14_11_17_1_6548 71 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 125 207 (accept_3_4 70 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 125 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 69 125 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 125 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 125 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 125 207 (accept_3_4 67 125 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 125 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 66
  125 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 125 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 65 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 125 207 (accept_3_4 64 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 125 207 (Polychromatic418967fa.accept_10_3_5_7_1_330 63 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 125 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 125 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 125 207 (accept_3_4 61 125 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 125 207 (Polychromatic418967fa.accept_16_12_13_15_1_1966 60 125 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 125 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 125 207 (accept_3_4 58 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 125 207 (Polychromatic418967fa.accept_11_2_4_9_1_484 57 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 125 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 125 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 125 207 (accept_3_4 55 125 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 125 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 125 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 125 207
  (Polychromatic418967fa.accept_10_3_5_7_1_330 53 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 125 207 (accept_3_4 52 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 125 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 125 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 125 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 125 207 (accept_3_4 49 125 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 125 207 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 125 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 125 207
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 125 207 (accept_3_4 46 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 125 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 125 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 125 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 125 207 (accept_3_4 43 125 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 125 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 125 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 125 207
  (Polychromatic418967fa.accept_36_5_17_27_1_12106 41 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 125 207 (accept_3_4 40 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 125 207 (Polychromatic418967fa.accept_15_9_5_12_1_1640 39 125 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 125 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 125 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 125 207 (accept_3_4 37 125 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 125 207
  (Polychromatic418967fa.accept_13_10_8_12_1_2032 36 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 125 207 (Polychromatic418967fa.accept_11_2_4_9_1_484 35 125 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 125 207 (accept_3_4 34 125 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 125 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 125 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 125 207 (accept_3_4 31 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 125 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 125 207 (Polychromatic418967fa.accept_20_9_5_7_1_6336 29 125 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 125 207 (accept_3_4 28 125 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 125 207 (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 125
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 125 207 (accept_3_4 25 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 125 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 125 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 125 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 207 (accept_3_4 22 125 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 125 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 125 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 125 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 125 207 (accept_3_4 19 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 125 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 125 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 125 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 207 (accept_3_4 16 125 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 125 207 (Polychromatic418967fa.accept_18_15_17_9_1_4200 15 125 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 125 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 125 207 (accept_3_4 13 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 125 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 125 207 (Polychromatic418967fa.accept_21_11_20_18_1_7656 11 125 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 207 (accept_3_4 10 125 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 125 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 125 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 125 207 (accept_3_4 7 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  125 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 125 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 125 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 207 (accept_3_4 4 125 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 125 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 207 (accept_3_4 1 125 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84 124 207 (Eq.refl
  Bool.true) (allA_succ_of_accept 83 124 207 (accept_3_5 83 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 124 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 82 124 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 124 207 (Polychromatic418967fa.accept_10_1_4_7_1_374 81 124
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 124 207 (accept_3_5 80 124
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 124 207
  (Polychromatic418967fa.accept_6_1_4_3_1_14 79 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 124 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 78 124 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 124 207 (accept_3_5 77 124 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 124 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 76 124 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 124 207 (Polychromatic418967fa.accept_8_3_4_7_1_475
  75 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 124 207 (accept_3_5 74
  124 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 124 207
  (Polychromatic418967fa.accept_6_1_4_3_1_14 73 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 124 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 124 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 124 207 (accept_3_5 71 124 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 124 207 (Polychromatic418967fa.accept_13_5_7_12_1_2757 70 124 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 124 207
  (Polychromatic418967fa.accept_7_6_5_4_1_297 69 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 124 207 (accept_3_5 68 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 124 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 124 207 (Polychromatic418967fa.accept_12_6_4_3_1_361 66 124 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 124 207 (accept_3_5 65 124 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 124 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 124 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 124 207
  (Polychromatic418967fa.accept_10_3_4_7_1_353 63 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 124 207 (accept_3_5 62 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 124 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 124 207 (Polychromatic418967fa.accept_13_8_7_12_1_3637 60 124 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 124 207 (accept_3_5 59 124 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 124 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 124 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 124 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 57 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 124 207 (accept_3_5 56 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 124 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 124 207 (Polychromatic418967fa.accept_12_6_4_3_1_361 54 124 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 124 207 (accept_3_5 53 124 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 124 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 52 124
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 124 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 124 207 (accept_3_5 50 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 124 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 124 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 124 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 124 207 (accept_3_5 47 124 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 124 207 (Polychromatic418967fa.accept_15_1_4_12_1_2401 46 124 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 124 207
  (Polychromatic418967fa.accept_13_6_7_12_1_3504 45 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 124 207 (accept_3_5 44 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 124 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 124 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 124 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 124 207 (accept_3_5 41 124 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 124 207 (Polychromatic418967fa.accept_16_8_12_15_1_2005 40 124
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 124 207
  (Polychromatic418967fa.accept_11_6_3_9_1_906 39 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 124 207 (accept_3_5 38 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 124 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 124 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 124 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 124 207 (accept_3_5 35 124 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 124 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 124 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 124 207
  (Polychromatic418967fa.accept_10_3_4_7_1_353 33 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 124 207 (accept_3_5 32 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 124 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 124 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 124 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 124 207 (accept_3_5 29 124 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 124 207 (Polychromatic418967fa.accept_11_6_3_9_1_906 28 124 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 124 207
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 124 207 (accept_3_5 26 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 124 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 124 207 (Polychromatic418967fa.accept_13_11_7_12_1_2758 24 124 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 124 207 (accept_3_5 23 124 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 124 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 124 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 124 207
  (Polychromatic418967fa.accept_10_1_4_7_1_374 21 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 124 207 (accept_3_5 20 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 124 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 124 207 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 124 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 124 207 (accept_3_5 17 124 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 124 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 124 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 124 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 124 207 (accept_3_5 14 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 124 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 124 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 124 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 124 207 (accept_3_5 11 124 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 124 207 (Polychromatic418967fa.accept_13_10_7_12_1_2782 10 124
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 124 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 124 207 (accept_3_5 8 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  124 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 124 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 124 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 124 207 (accept_3_5 5 124 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 124 207 (Polychromatic418967fa.accept_13_4_7_12_1_2823 4 124 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 124 207
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 124 207 (accept_3_5 2 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  124 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 124 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 124 207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 85 123 207 (Eq.refl Bool.true) (allA_succ_of_gcd 84 123 207 3 28 41 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 123 207
  (Polychromatic418967fa.accept_13_5_6_12_1_2750 83 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 123 207 (Polychromatic418967fa.accept_15_7_3_12_1_365 82 123 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 123 207 3 27 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 123 207 (Polychromatic418967fa.accept_13_2_6_12_1_1334
  80 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 123 207
  (Polychromatic418967fa.accept_25_4_23_7_1_12105 79 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 123 207 3 26 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 123 207 (Polychromatic418967fa.accept_15_2_3_12_1_891 77 123 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 123 207
  (Polychromatic418967fa.accept_8_4_3_7_1_491 76 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 123 207 3 25 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 123 207 (Polychromatic418967fa.accept_10_4_3_7_1_1110 74 123 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 123 207
  (Polychromatic418967fa.accept_11_7_2_9_1_480 73 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 123 207 3 24 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 123 207 (Polychromatic418967fa.accept_16_7_11_15_1_2929 71 123 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 123 207
  (Polychromatic418967fa.accept_11_4_2_9_1_496 70 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 123 207 3 23 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 123 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 68 123 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 123 207
  (Polychromatic418967fa.accept_13_2_6_12_1_1334 67 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 123 207 3 22 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 123 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 65 123 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 123 207
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 64 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 123 207 3 21 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 123 207 (Polychromatic418967fa.accept_11_7_2_9_1_480 62 123 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 123 207
  (Polychromatic418967fa.accept_26_9_19_25_1_12104 61 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 123 207 3 20 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 123 207 (Polychromatic418967fa.accept_11_4_2_9_1_496 59 123 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 123 207
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 58 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 57 123 207 3 19 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 56 123 207 (Polychromatic418967fa.accept_10_6_3_7_1_2197 56 123 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 207
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 55 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 123 207 3 18 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 123 207 (Polychromatic418967fa.accept_15_8_3_12_1_1657 53 123 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 123 207
  (Polychromatic418967fa.accept_8_4_3_7_1_491 52 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 123 207 3 17 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 123 207 (Polychromatic418967fa.accept_17_16_4_3_1_3429 50 123 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 207
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 49 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 123 207 3 16 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 123 207 (Polychromatic418967fa.accept_15_2_3_12_1_891 47 123 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 123 207
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 46 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 123 207 3 15 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 123 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 44 123 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 207
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 43 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 123 207 3 14 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 123 207 (Polychromatic418967fa.accept_13_2_6_12_1_1334 41 123 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 123 207
  (Polychromatic418967fa.accept_11_7_2_9_1_480 40 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 123 207 3 13 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 123 207 (Polychromatic418967fa.accept_15_8_3_12_1_1657 38 123 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 207
  (Polychromatic418967fa.accept_11_4_2_9_1_496 37 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 123 207 3 12 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 123 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 123 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 207
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 34 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 123 207 3 11 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 123 207 (Polychromatic418967fa.accept_15_2_3_12_1_891 32 123 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 207
  (Polychromatic418967fa.accept_13_5_6_12_1_2750 31 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 123 207 3 10 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 123 207 (Polychromatic418967fa.accept_11_7_2_9_1_480 29 123 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 207 (Polychromatic418967fa.accept_8_4_3_7_1_491
  28 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 123 207 3 9 41 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 123 207
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 26 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 123 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 123 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 123 207 3 8 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 123 207
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 23 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 123 207 (Polychromatic418967fa.accept_15_7_3_12_1_365 22 123 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 123 207 3 7 41 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 123 207
  (Polychromatic418967fa.accept_8_4_3_7_1_491 20 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 123 207 (Polychromatic418967fa.accept_16_3_11_15_1_1963 19 123 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 123 207 3 6 41 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 123 207
  (Polychromatic418967fa.accept_15_2_3_12_1_891 17 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 207 (Polychromatic418967fa.accept_10_6_3_7_1_2197 16 123 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 123 207 3 5 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 123 207 (Polychromatic418967fa.accept_10_4_3_7_1_1110
  14 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 207
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 123 207 3 4 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 123 207 (Polychromatic418967fa.accept_18_11_15_9_1_360 11 123 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 207
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 10 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 123 207 3 3 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 123 207 (Polychromatic418967fa.accept_15_8_3_12_1_1657 8 123 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 207 (Polychromatic418967fa.accept_11_7_2_9_1_480 7
  123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 123 207 3 2 41 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 123 207
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 123 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 123 207 3 1 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 123 207 (Polychromatic418967fa.accept_13_2_6_12_1_1334 2 123 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 207
  (Polychromatic418967fa.accept_16_1_11_15_1_498 1 123 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 123 207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86
  122 207 (Eq.refl Bool.true) (allA_succ_of_accept 85 122 207 (accept_3_4 85 122 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 122 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 84 122 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 122 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 122 207 (accept_3_4 82 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 122 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 122 207 (Polychromatic418967fa.accept_13_2_5_12_1_2043 80 122 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 122 207 (accept_3_4 79 122 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 122 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 122 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 122 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 122 207 (accept_3_4 76 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 122 207 (Polychromatic418967fa.accept_10_5_2_7_1_345 75 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 122 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 74 122 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 122 207 (accept_3_4 73 122 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 122 207 (Polychromatic418967fa.accept_13_7_5_12_1_1305 72 122
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 122 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 122 207 (accept_3_4 70 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 122 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 122 207 (Polychromatic418967fa.accept_19_11_8_17_1_12103 68 122 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 122 207 (accept_3_4 67 122 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 122 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 66 122
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 122 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 122 207 (accept_3_4 64 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 122 207 (Polychromatic418967fa.accept_14_7_10_11_1_8112 63 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 122 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 62 122 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 122 207 (accept_3_4 61 122 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 122 207 (Polychromatic418967fa.accept_13_8_5_12_1_2755 60 122 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 122 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 122 207 (accept_3_4 58 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 122 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 122 207 (Polychromatic418967fa.accept_13_4_5_12_1_751 56 122 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 122 207 (accept_3_4 55 122 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 122 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 54 122
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 122 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 122 207 (accept_3_4 52 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 122 207 (Polychromatic418967fa.accept_15_6_2_12_1_885 51 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 122 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 50 122 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 122 207 (accept_3_4 49 122 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 122 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 122 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 122 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 122 207 (accept_3_4 46 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 122 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 122 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 44 122 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 122 207 (accept_3_4 43 122 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 122 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 122
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 122 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 122 207 (accept_3_4 40 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 122 207 (Polychromatic418967fa.accept_10_9_2_7_1_1096 39 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 122 207 (Polychromatic418967fa.accept_20_18_2_7_1_6285 38 122 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 122 207 (accept_3_4 37 122 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 122 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 122 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 122 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 122 207 (accept_3_4 34 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 122 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 122 207 (Polychromatic418967fa.accept_11_10_1_9_1_2060 32 122 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 122 207 (accept_3_4 31 122 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 122 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 122
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 122 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 122 207 (accept_3_4 28 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 122 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 122 207 (Polychromatic418967fa.accept_25_1_22_7_1_12086 26 122 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 122 207 (accept_3_4 25 122 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 122 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 122
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 122 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 122 207 (accept_3_4 22 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 122 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 122 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 122 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 122 207 (accept_3_4 19 122 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 122 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 122 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 122 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 122 207 (accept_3_4 16 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 122 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 122 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 122 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 122 207 (accept_3_4 13 122 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 122 207 (Polychromatic418967fa.accept_20_12_2_7_1_4788 12 122
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 122 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 122 207 (accept_3_4 10 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  122 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 122 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 122 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 122 207 (accept_3_4 7 122 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 122 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 122 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 122 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 122 207 (accept_3_4 4 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  122 207 (Polychromatic418967fa.accept_15_3_2_12_1_2469 3 122 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 122 207 (Polychromatic418967fa.accept_13_2_5_12_1_2043 2 122 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 122 207 (accept_3_4 1 122 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 122
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 121 207
  (Eq.refl Bool.true) (allA_succ_of_accept 86 121 207 (accept_3_5 86 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 121 207 (Polychromatic418967fa.accept_13_7_4_12_1_1341 85 121 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 121 207 (Polychromatic418967fa.accept_10_4_1_7_1_371 84 121
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 121 207 (accept_3_5 83 121
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 121 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 82 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 121 207 (Polychromatic418967fa.accept_12_9_1_3_1_350 81 121 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 121 207 (accept_3_5 80 121 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 121 207 (Polychromatic418967fa.accept_15_4_1_12_1_914 79 121 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 121 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 121 207 (accept_3_5 77 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 121 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 121 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 75 121 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 121 207 (accept_3_5 74 121 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 121 207 (Polychromatic418967fa.accept_13_8_4_12_1_2753 73 121 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 121 207
  (Polychromatic418967fa.accept_13_7_4_12_1_1341 72 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 121 207 (accept_3_5 71 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 121 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 121 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 121 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 121 207 (accept_3_5 68 121 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 121 207 (Polychromatic418967fa.accept_13_2_4_12_1_745 67 121 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 121 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 121 207 (accept_3_5 65 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 121 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 121 207 (Polychromatic418967fa.accept_13_11_4_12_1_3585 63 121 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 121 207 (accept_3_5 62 121 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 121 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 121 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 121 207
  (Polychromatic418967fa.accept_13_8_4_12_1_2753 60 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 121 207 (accept_3_5 59 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 121 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 121 207 (Polychromatic418967fa.accept_12_9_1_3_1_350 57 121 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 121 207 (accept_3_5 56 121 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 121 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 121 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 121 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 121 207 (accept_3_5 53 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 121 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 121 207 (Polychromatic418967fa.accept_19_13_7_17_1_9441 51 121 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 121 207 (accept_3_5 50 121 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 121 207 (Polychromatic418967fa.accept_15_4_1_12_1_914 49 121
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 121 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 121 207 (accept_3_5 47 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 121 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 121 207 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 121 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 121 207 (accept_3_5 44 121 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 121 207 (Polychromatic418967fa.accept_15_13_1_12_1_1638 43 121
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 121 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 121 207 (accept_3_5 41 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 121 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 121 207 (Polychromatic418967fa.accept_17_5_2_3_1_9775 39 121 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 121 207 (accept_3_5 38 121 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 121 207 (Polychromatic418967fa.accept_13_11_4_12_1_3585 37 121
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 121 207
  (Polychromatic418967fa.accept_10_6_1_7_1_342 36 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 121 207 (accept_3_5 35 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 121 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 121 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 121 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 121 207 (accept_3_5 32 121 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 121 207 (Polychromatic418967fa.accept_13_5_4_12_1_2058 31 121 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 121 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 121 207 (accept_3_5 29 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 121 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 121 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 121 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 121 207 (accept_3_5 26 121 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 121 207 (Polychromatic418967fa.accept_22_3_11_9_1_12102 25 121 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 121 207
  (Polychromatic418967fa.accept_10_4_1_7_1_371 24 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 121 207 (accept_3_5 23 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 121 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 121 207 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 121 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 207 (accept_3_5 20 121 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 121 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 121 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 121 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 121 207 (accept_3_5 17 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 121 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 121 207 (Polychromatic418967fa.accept_13_2_4_12_1_745 15 121 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 121 207 (accept_3_5 14 121 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 121 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 121 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 121 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 121 207 (accept_3_5 11 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 121 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 121 207 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 121 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 207 (accept_3_5 8 121 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 121 207 (Polychromatic418967fa.accept_13_7_4_12_1_1341 7 121 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 121 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 121 207 (accept_3_5 5 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  121 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 121 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 121 207 (Polychromatic418967fa.accept_13_3_4_12_1_36 3 121 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 207 (accept_3_5 2 121 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 207 (Polychromatic418967fa.accept_17_1_2_3_1_4668 1 121 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 121
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 120 207
  (Eq.refl Bool.true) (allA_succ_of_gcd 87 120 207 3 29 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 120 207 (Polychromatic418967fa.accept_21_2_15_18_1_806 86 120
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 120 207
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 85 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 120 207 3 28 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 120 207 (Polychromatic418967fa.accept_17_15_1_3_1_1488 83 120 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 120 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 82 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 120 207 3 27 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 120 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 80 120 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 120 207
  (Polychromatic418967fa.accept_19_3_6_17_1_6579 79 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 120 207 3 26 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 120 207 (Polychromatic418967fa.accept_17_9_1_3_1_4626 77 120 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 120 207
  (Polychromatic418967fa.accept_16_12_8_15_1_5119 76 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 75 120 207 3 25 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 120 207 (Polychromatic418967fa.accept_11_8_10_9_1_1401 74 120 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 120 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 73 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 120 207 3 24 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 120 207 (Polychromatic418967fa.accept_16_7_8_15_1_6327 71 120 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 120 207
  (Polychromatic418967fa.accept_17_2_1_3_1_2357 70 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 120 207 3 23 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 120 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 68 120 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 120 207 (Polychromatic418967fa.accept_11_1_10_9_1_871
  67 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 120 207 3 22 40 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 120 207
  (Polychromatic418967fa.accept_16_1_8_15_1_1945 65 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 120 207 (Polychromatic418967fa.accept_18_10_12_9_1_2012 64 120 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 120 207 3 21 40 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 120 207
  (Polychromatic418967fa.accept_21_20_15_18_1_4457 62 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 120 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 61 120 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 120 207 3 20 40 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 120 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 59 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 120 207 (Polychromatic418967fa.accept_18_4_12_9_1_2011 58 120 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 120 207 3 19 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 120 207 (Polychromatic418967fa.accept_11_1_10_9_1_871
  56 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 120 207
  (Polychromatic418967fa.accept_16_7_8_15_1_6327 55 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 120 207 3 18 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 120 207 (Polychromatic418967fa.accept_17_2_1_3_1_2357 53 120 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 120 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 52 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 120 207 3 17 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 120 207 (Polychromatic418967fa.accept_19_12_6_17_1_12061 50 120 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 120 207
  (Polychromatic418967fa.accept_16_1_8_15_1_1945 49 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 120 207 3 16 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 120 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 120 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 120 207 (Polychromatic418967fa.accept_14_4_8_11_1_794
  46 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 120 207 3 15 40 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 120 207
  (Polychromatic418967fa.accept_16_12_8_15_1_5119 44 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 120 207 (Polychromatic418967fa.accept_13_4_3_12_1_2066 43 120 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 120 207 3 14 40 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 120 207
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 41 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 120 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 120 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 120 207 3 13 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 120 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 38
  120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 120 207
  (Polychromatic418967fa.accept_19_18_6_17_1_8078 37 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 120 207 3 12 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 120 207 (Polychromatic418967fa.accept_13_9_3_12_1_2025 35 120 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 120 207
  (Polychromatic418967fa.accept_11_1_10_9_1_871 34 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 120 207 3 11 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 120 207 (Polychromatic418967fa.accept_14_4_8_11_1_794 32 120 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 120 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 120 207 3 10 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 120 207 (Polychromatic418967fa.accept_18_11_12_9_1_992 29 120 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 207
  (Polychromatic418967fa.accept_13_2_3_12_1_735 28 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 120 207 3 9 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 120 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 120 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 120 207 (Polychromatic418967fa.accept_16_9_8_15_1_5095 25 120
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 120 207 3 8 40 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 207
  (Polychromatic418967fa.accept_11_1_10_9_1_871 23 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 120 207 (Polychromatic418967fa.accept_13_9_3_12_1_2025 22 120 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 120 207 3 7 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 120 207 (Polychromatic418967fa.accept_16_4_8_15_1_1113
  20 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 120 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 120 207 3 6 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 120 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 120 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 207 (Polychromatic418967fa.accept_18_16_12_9_1_5504 16 120
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 120 207 3 5 40 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 120 207
  (Polychromatic418967fa.accept_21_14_15_18_1_1749 14 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 120 207 (Polychromatic418967fa.accept_19_13_6_17_1_12101 13 120 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 207 3 4 40 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 207
  (Polychromatic418967fa.accept_18_11_12_9_1_992 11 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 120 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 120 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 120 207 3 3 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 120 207 (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 120 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 207
  (Polychromatic418967fa.accept_16_7_8_15_1_6327 7 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 120 207 3 2 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 120 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 120 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 120 207 (Polychromatic418967fa.accept_13_4_3_12_1_2066 4 120
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 120 207 3 1 40 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 120 207
  (Polychromatic418967fa.accept_13_2_3_12_1_735 2 120 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 120 207 (Polychromatic418967fa.accept_11_1_10_9_1_871 1 120 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 120
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 119 207
  (Eq.refl Bool.true) (allA_succ_of_accept 88 119 207 (accept_3_4 88 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 119 207 (Polychromatic418967fa.accept_14_3_7_11_1_765 87 119 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 119 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 86 119 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 119 207 (accept_3_4 85 119 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 119 207
  (Polychromatic418967fa.accept_13_6_2_12_1_2802 84 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 119 207 (Polychromatic418967fa.accept_13_5_2_12_1_1301 83 119 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 119 207 (accept_3_4 82 119 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 119 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 81 119 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 119 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 80 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 119 207 (accept_3_4 79 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 119 207 (Polychromatic418967fa.accept_10_8_9_7_1_1118 78 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 119 207 (Polychromatic418967fa.accept_15_2_14_12_1_2453 77 119 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 119 207 (accept_3_4 76 119 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 119 207 (Polychromatic418967fa.accept_13_10_2_12_1_1332 75 119
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 119 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 74 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 119 207 (accept_3_4 73 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 119 207 (Polychromatic418967fa.accept_10_2_9_7_1_720 72 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 119 207 (Polychromatic418967fa.accept_13_6_2_12_1_2802 71 119 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 119 207 (accept_3_4 70 119 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 119 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 69 119
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 119 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 119 207 (accept_3_4 67 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 119 207 (Polychromatic418967fa.accept_13_1_2_12_1_1299 66 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 119 207 (Polychromatic418967fa.accept_25_15_19_7_1_12100 65 119 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 119 207 (accept_3_4 64 119 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 119 207 (Polychromatic418967fa.accept_25_13_19_7_1_6688 63 119
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 119 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 62 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 119 207 (accept_3_4 61 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 119 207 (Polychromatic418967fa.accept_14_4_7_11_1_790 60 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 119 207 (Polychromatic418967fa.accept_14_3_7_11_1_765 59 119 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 119 207 (accept_3_4 58 119 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 119 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 57 119
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 119 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 119 207 (accept_3_4 55 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 119 207 (Polychromatic418967fa.accept_15_9_14_12_1_913 54 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 119 207 (Polychromatic418967fa.accept_13_1_2_12_1_1299 53 119 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 119 207 (accept_3_4 52 119 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 119 207 (Polychromatic418967fa.accept_16_3_7_15_1_1130 51 119
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 119 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 119 207 (accept_3_4 49 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 119 207 (Polychromatic418967fa.accept_10_8_9_7_1_1118 48 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 119 207 (Polychromatic418967fa.accept_15_2_14_12_1_2453 47 119 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 207 (accept_3_4 46 119 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 119 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 119
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 119 207 (accept_3_4 43 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 119 207 (Polychromatic418967fa.accept_10_2_9_7_1_720 42 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 119 207 (Polychromatic418967fa.accept_15_11_14_12_1_2458 41 119 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 207 (accept_3_4 40 119 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 207 (Polychromatic418967fa.accept_15_9_14_12_1_913 39 119
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 119 207 (accept_3_4 37 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 119 207 (Polychromatic418967fa.accept_13_10_2_12_1_1332 36 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 119 207 (Polychromatic418967fa.accept_16_3_7_15_1_1130 35 119 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 207 (accept_3_4 34 119 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 119
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 119 207 (accept_3_4 31 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 119 207 (Polychromatic418967fa.accept_13_4_2_12_1_2800 30 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 119 207 (Polychromatic418967fa.accept_13_3_2_12_1_2797 29 119 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 207 (accept_3_4 28 119 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 207 (Polychromatic418967fa.accept_13_1_2_12_1_1299 27 119
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 119 207 (accept_3_4 25 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 119 207 (Polychromatic418967fa.accept_14_10_7_11_1_3015 24 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 119 207 (Polychromatic418967fa.accept_13_10_2_12_1_1332 23 119 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 207 (accept_3_4 22 119 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 119
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 207 (accept_3_4 19 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 207 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 119 207 (Polychromatic418967fa.accept_13_4_2_12_1_2800 17 119 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 207 (accept_3_4 16 119 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 207 (Polychromatic418967fa.accept_18_15_11_9_1_4256 15 119
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 119 207 (accept_3_4 13 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 207 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 207 (Polychromatic418967fa.accept_15_11_14_12_1_2458 11 119 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 207 (accept_3_4 10 119 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 119 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 207 (accept_3_4 7 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 207 (Polychromatic418967fa.accept_13_6_2_12_1_2802 6 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 207 (Polychromatic418967fa.accept_13_5_2_12_1_1301 5 119 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 207 (accept_3_4 4 119 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 207 (Polychromatic418967fa.accept_13_3_2_12_1_2797 3 119
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 207 (accept_3_4 1 119 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 90 118 207
  (Eq.refl Bool.true) (allA_succ_of_accept 89 118 207 (accept_3_5 89 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 118 207 (Polychromatic418967fa.accept_21_4_13_18_1_137 88 118 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 118 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 87 118 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 118 207 (accept_3_5 86 118 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 118 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 85
  118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 118 207
  (Polychromatic418967fa.accept_18_12_10_9_1_5497 84 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 118 207 (accept_3_5 83 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 118 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 82 118 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 118 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 118 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 118 207 (accept_3_5 80 118 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 118 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 79
  118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 118 207
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 78 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 118 207 (accept_3_5 77 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 118 207 (Polychromatic418967fa.accept_11_10_8_9_1_492 76 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 118 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 118 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 118 207 (accept_3_5 74 118 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 118 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 118 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 118 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 72 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 118 207 (accept_3_5 71 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 118 207 (Polychromatic418967fa.accept_13_5_1_12_1_740 70 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 118 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 118 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 118 207 (accept_3_5 68 118 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 118 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 118 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 118 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 66 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 118 207 (accept_3_5 65 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 118 207 (Polychromatic418967fa.accept_17_13_16_3_1_1431 64 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 118 207 (Polychromatic418967fa.accept_13_11_1_12_1_742 63 118 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 118 207 (accept_3_5 62 118 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 118 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 118 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 118 207
  (Polychromatic418967fa.accept_13_8_1_12_1_762 60 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 118 207 (accept_3_5 59 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 118 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 118 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 118 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 118 207 (accept_3_5 56 118 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 118 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 118 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 118 207
  (Polychromatic418967fa.accept_7_5_6_4_1_117 54 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 118 207 (accept_3_5 53 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 118 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 118 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 118 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 118 207 (accept_3_5 50 118 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 118 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 118 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 118 207
  (Polychromatic418967fa.accept_15_3_13_12_1_348 48 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 118 207 (accept_3_5 47 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 118 207 (Polychromatic418967fa.accept_15_1_13_12_1_347 46 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 118 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 118 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 118 207 (accept_3_5 44 118 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 118 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 118 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 118 207
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 118 207 (accept_3_5 41 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 118 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 118 207 (Polychromatic418967fa.accept_10_9_8_7_1_714 39 118 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 118 207 (accept_3_5 38 118 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 118 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 118 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 118 207
  (Polychromatic418967fa.accept_21_15_13_18_1_7523 36 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 118 207 (accept_3_5 35 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 118 207 (Polychromatic418967fa.accept_13_8_1_12_1_762 34 118 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 118 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 118 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 118 207 (accept_3_5 32 118 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 118 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 31
  118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 118 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 118 207 (accept_3_5 29 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 118 207 (Polychromatic418967fa.accept_13_2_1_12_1_1326 28 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 118 207 (Polychromatic418967fa.accept_19_8_4_17_1_9510 27 118 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 118 207 (accept_3_5 26 118 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 118 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 118 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 118 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 118 207 (accept_3_5 23 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 118 207 (Polychromatic418967fa.accept_20_2_18_7_1_3394 22 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 118 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 118 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 118 207 (accept_3_5 20 118 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 118 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 118 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 118 207
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 118 207 (accept_3_5 17 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 118 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 118 207 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 118 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 118 207 (accept_3_5 14 118 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 118 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 118 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 118 207
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 118 207 (accept_3_5 11 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 118 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 118 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 118 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 118 207 (accept_3_5 8 118 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 118 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 118 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 118 207
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 118 207 (accept_3_5 5 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  118 207 (Polychromatic418967fa.accept_17_4_16_3_1_4620 4 118 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 118 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 118 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 118 207 (accept_3_5 2 118 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 118 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 118 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 117 207
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 117 207 9 10 13 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 117 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 89 117 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 117 207
  (Polychromatic418967fa.accept_19_12_3_17_1_5182 88 117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 87 117 207 3 29 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 86 117 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 117 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 117 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 85 117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 117 207 3 28 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 117 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 83 117 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 117 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 82
  117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 117 207 9 9 13 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 117 207
  (Polychromatic418967fa.accept_17_12_15_3_1_7168 80 117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 117 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 79 117 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 117 207 3 26 39 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 117 207
  (Polychromatic418967fa.accept_12_5_9_3_1_85 77 117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 117 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 76 117 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 117 207 3 25 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 117 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 74
  117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 207
  (Polychromatic418967fa.accept_12_1_9_3_1_370 73 117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 117 207 9 8 13 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 117 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 71 117 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 117 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 117 207 3 23 39 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 117 207
  (Polychromatic418967fa.accept_11_2_7_9_1_890 68 117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 117 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 67 117 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 117 207 3 22 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 117 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 65
  117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 117 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 64 117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 117 207 9 7 13 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 117 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 117 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 207 (Polychromatic418967fa.accept_12_1_9_3_1_370 61 117
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 117 207 3 20 39 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 117 207
  (Polychromatic418967fa.accept_12_11_9_3_1_792 59 117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 117 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 117 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 117 207 3 19 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 117 207
  (Polychromatic418967fa.accept_20_16_17_7_1_7845 56 117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 117 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 117 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 117 207 9 6 13 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 117 207
  (Polychromatic418967fa.accept_12_5_9_3_1_85 53 117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 117 207 (Polychromatic418967fa.accept_16_4_5_15_1_5083 52 117 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 117 207 3 17 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 117 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 50
  117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 207
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 49 117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 117 207 3 16 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 117 207 (Polychromatic418967fa.accept_12_11_9_3_1_792 47 117 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 117 207 9 5 13 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 117 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 117 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 117 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 117 207 3 14 39 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 117 207
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 207 (Polychromatic418967fa.accept_19_2_3_17_1_5146 40 117 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 117 207 3 13 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 117 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 117 207 9 4 13 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 117 207 (Polychromatic418967fa.accept_11_2_7_9_1_890 35 117 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 117 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 117 207 3 11 39 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 117 207
  (Polychromatic418967fa.accept_20_12_17_7_1_4786 32 117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 117 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 31 117 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 117 207 3 10 39 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 117 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 117 207 (Polychromatic418967fa.accept_20_8_17_7_1_12099 28 117 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 117 207 9 3 13 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 117 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 117 207 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 117 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 117 207 3 8 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 117 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 23
  117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 117 207 3 7 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 117 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 117 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 117
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 117 207 9 2 13 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 117 207
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 117 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 117 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 117 207 3 5 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 117 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 207
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 117 207 3 4 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 117 207 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 117 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 117 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 117 207 9 1 13 23 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 117 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 117 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 117 207 3 2 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 117 207 (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 117 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 207
  (Polychromatic418967fa.accept_16_4_5_15_1_5083 4 117 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 117 207 3 1 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 117 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 117 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 117 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 116 207
  (Eq.refl Bool.true) (allA_succ_of_accept 91 116 207 (accept_3_4 91 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 116 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 90 116 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 116 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 89 116 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 116 207 (accept_3_4 88 116 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 116 207
  (Polychromatic418967fa.accept_17_2_14_3_1_4679 87 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 116 207 (Polychromatic418967fa.accept_19_10_2_17_1_675 86 116 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 116 207 (accept_3_4 85 116 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 116 207 (Polychromatic418967fa.accept_25_9_16_7_1_12098 84 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 116 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 116 207 (accept_3_4 82 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 116 207 (Polychromatic418967fa.accept_10_1_6_7_1_710 81 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 116 207 (Polychromatic418967fa.accept_11_3_6_9_1_1378 80 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 116 207 (accept_3_4 79 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 116 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 78 116 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 116 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 77 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 116 207 (accept_3_4 76 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 116 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 75 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 116 207 (Polychromatic418967fa.accept_15_14_11_12_1_4440 74 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 116 207 (accept_3_4 73 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 116 207 (Polychromatic418967fa.accept_16_8_4_15_1_2941 72 116
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 116 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 116 207 (accept_3_4 70 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 116 207 (Polychromatic418967fa.accept_11_3_6_9_1_1378 69 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 116 207 (Polychromatic418967fa.accept_15_8_11_12_1_1626 68 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 116 207 (accept_3_4 67 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 116 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 66 116 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 116 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 65 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 116 207 (accept_3_4 64 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 116 207 (Polychromatic418967fa.accept_10_3_6_7_1_2188 63 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 116 207 (Polychromatic418967fa.accept_16_14_4_15_1_3944 62 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 116 207 (accept_3_4 61 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 116 207 (Polychromatic418967fa.accept_16_12_4_15_1_5091 60 116
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 116 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 116 207 (accept_3_4 58 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 116 207 (Polychromatic418967fa.accept_14_1_4_11_1_3036 57 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 116 207 (Polychromatic418967fa.accept_16_8_4_15_1_2941 56 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 116 207 (accept_3_4 55 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 116 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 116 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 116 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 116 207 (accept_3_4 52 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 116 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 116 207 (Polychromatic418967fa.accept_14_8_4_11_1_3035 50 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 116 207 (accept_3_4 49 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 116 207 (Polychromatic418967fa.accept_19_10_2_17_1_675 48 116
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 116 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 116 207 (accept_3_4 46 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 116 207 (Polychromatic418967fa.accept_17_11_14_3_1_1427 45 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 116 207 (Polychromatic418967fa.accept_15_14_11_12_1_4440 44 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 116 207 (accept_3_4 43 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 116 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 116 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 116 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 116 207 (accept_3_4 40 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 116 207 (Polychromatic418967fa.accept_18_3_8_9_1_1956 39 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 116 207 (Polychromatic418967fa.accept_15_8_11_12_1_1626 38 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 116 207 (accept_3_4 37 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 116 207 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 116
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 116 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 116 207 (accept_3_4 34 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 116 207 (Polychromatic418967fa.accept_10_3_6_7_1_2188 33 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 116 207 (Polychromatic418967fa.accept_17_15_14_3_1_5947 32 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 116 207 (accept_3_4 31 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 116 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 116 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 116 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 116 207 (accept_3_4 28 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 116 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 116 207 (Polychromatic418967fa.accept_19_7_2_17_1_9426 26 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 116 207 (accept_3_4 25 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 116 207 (Polychromatic418967fa.accept_16_8_4_15_1_2941 24 116
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 116 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 116 207 (accept_3_4 22 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 116 207 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 116 207 (Polychromatic418967fa.accept_21_20_11_18_1_3037 20 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 116 207 (accept_3_4 19 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 116 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 116 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 116 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 116 207 (accept_3_4 16 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 116 207 (Polychromatic418967fa.accept_14_1_4_11_1_3036 15 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 116 207 (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 116 207 (accept_3_4 13 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 116 207 (Polychromatic418967fa.accept_16_12_4_15_1_5091 12 116
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 116 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 116 207 (accept_3_4 10 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  116 207 (Polychromatic418967fa.accept_19_9_2_17_1_10805 9 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 116 207 (Polychromatic418967fa.accept_14_8_4_11_1_3035 8 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 116 207 (accept_3_4 7 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 116 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 116 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 116 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 116 207 (accept_3_4 4 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  116 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 116 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 116 207 (Polychromatic418967fa.accept_17_2_14_3_1_4679 2 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 116 207 (accept_3_4 1 116 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 116
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 93 115 207
  (Eq.refl Bool.true) (allA_succ_of_gcd 92 115 207 23 4 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 115 207 (Polychromatic418967fa.accept_14_7_3_11_1_2199 91 115 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 115 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 90 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 115 207 (accept_3_5 89 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 115 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 115 207 (Polychromatic418967fa.accept_16_7_3_15_1_2940 87 115 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 115 207 (accept_3_5 86 115 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 115 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 85 115 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 115 207
  (Polychromatic418967fa.accept_8_4_3_7_1_491 84 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 115 207 (accept_3_5 83 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 115 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 115 207 (Polychromatic418967fa.accept_12_9_7_3_1_1309 81 115 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 115 207 (accept_3_5 80 115 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 115 207 (Polychromatic418967fa.accept_13_1_11_12_1_1322 79 115
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 115 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 78 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 115 207 (accept_3_5 77 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 115 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 115 207 (Polychromatic418967fa.accept_13_10_11_12_1_1320 75 115 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 115 207 (accept_3_5 74 115 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 115 207 (Polychromatic418967fa.accept_10_3_5_7_1_330 73 115
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 115 207
  (Polychromatic418967fa.accept_10_2_5_7_1_1124 72 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 115 207 (accept_3_5 71 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 115 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 69 115 207 23 3 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 115 207 (accept_3_5 68 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 115 207 (Polychromatic418967fa.accept_15_7_10_12_1_2403 67 115 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 115 207
  (Polychromatic418967fa.accept_13_1_11_12_1_1322 66 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 115 207 (accept_3_5 65 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 115 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 115 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 115 207 (Polychromatic418967fa.accept_10_3_5_7_1_330 63 115
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 115 207 (accept_3_5 62 115
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 115 207
  (Polychromatic418967fa.accept_16_13_3_15_1_1931 61 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 115 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 115 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 115 207 (accept_3_5 59 115 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 115 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 115 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 115 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 115 207 (accept_3_5 56 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 115 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 115 207 (Polychromatic418967fa.accept_15_9_10_12_1_1625 54 115 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 115 207 (accept_3_5 53 115 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 115 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 115 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 115 207
  (Polychromatic418967fa.accept_11_7_5_9_1_884 51 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 115 207 (accept_3_5 50 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 115 207 (Polychromatic418967fa.accept_13_10_11_12_1_1320 49 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 115 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 115 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 115 207 (accept_3_5 47 115 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 115 207 23 2 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 115 207 (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 115
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 115 207 (accept_3_5 44 115
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 115 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 115 207 (Polychromatic418967fa.accept_10_2_5_7_1_1124 42 115 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 207 (accept_3_5 41 115 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 115 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 115 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 115 207
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 39 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 115 207 (accept_3_5 38 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 115 207 (Polychromatic418967fa.accept_15_7_10_12_1_2403 37 115 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 115 207 (Polychromatic418967fa.accept_7_1_3_4_1_128
  36 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 115 207 (accept_3_5 35
  115 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 115 207
  (Polychromatic418967fa.accept_6_4_1_3_1_77 34 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 115 207 (Polychromatic418967fa.accept_10_3_5_7_1_330 33 115 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 207 (accept_3_5 32 115 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 115 207 (Polychromatic418967fa.accept_24_7_19_15_1_12097 31 115 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 115 207
  (Polychromatic418967fa.accept_13_4_11_12_1_1318 30 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 115 207 (accept_3_5 29 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 115 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 115 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 115 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 207 (accept_3_5 26 115 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 115 207
  (Polychromatic418967fa.accept_17_8_13_3_1_3432 25 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 115 207 (Polychromatic418967fa.accept_15_9_10_12_1_1625 24 115 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 23 115 207 23 1 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 22 115 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 22
  115 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 207
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 115 207 (accept_3_5 20 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 115 207 (Polychromatic418967fa.accept_25_19_15_7_1_12096 19 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 115 207 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 115 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 207 (accept_3_5 17 115 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 115 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 115 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 115 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 115 207 (accept_3_5 14 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 115 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 115 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 115 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 207 (accept_3_5 11 115 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 115 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 115 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 115 207
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 115 207 (accept_3_5 8 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  115 207 (Polychromatic418967fa.accept_11_7_5_9_1_884 7 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 115 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 115 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 115 207 (accept_3_5 5 115 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 115 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 115 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 207
  (Polychromatic418967fa.accept_10_3_5_7_1_330 3 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 115 207 (accept_3_5 2 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  115 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 115 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 115
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 94 114
  207 (Eq.refl Bool.true) (allA_succ_of_gcd 93 114 207 3 31 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 114 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 92 114 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 114 207
  (Polychromatic418967fa.accept_10_1_4_7_1_374 91 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 114 207 3 30 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 114 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 114 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 114 207 (Polychromatic418967fa.accept_12_4_6_3_1_332
  88 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 114 207 3 29 38 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 114 207
  (Polychromatic418967fa.accept_12_2_6_3_1_331 86 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 114 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 114 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 114 207 3 28 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 114 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 83
  114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 114 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 82 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 114 207 3 27 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 114 207 (Polychromatic418967fa.accept_12_8_6_3_1_366 80 114 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 114 207 (Polychromatic418967fa.accept_11_2_4_9_1_484
  79 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 114 207 3 26 38 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 114 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 114 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 76 114 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 114 207 3 25 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 114 207 (Polychromatic418967fa.accept_12_2_6_3_1_331
  74 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 114 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 73 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 114 207 3 24 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 114 207 (Polychromatic418967fa.accept_10_1_4_7_1_374 71 114 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 114 207 (Polychromatic418967fa.accept_12_10_6_3_1_786
  70 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 114 207 3 23 38 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 114 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 68 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 114 207 (Polychromatic418967fa.accept_13_2_10_12_1_757 67 114 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 114 207 3 22 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 114 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 65
  114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 114 207
  (Polychromatic418967fa.accept_12_4_6_3_1_332 64 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 114 207 3 21 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 114 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 62 114 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 114 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 61
  114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 114 207 3 20 38 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 114 207
  (Polychromatic418967fa.accept_13_7_10_12_1_2047 59 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 114 207 (Polychromatic418967fa.accept_12_10_6_3_1_786 58 114 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 114 207 3 19 38 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 114 207
  (Polychromatic418967fa.accept_12_8_6_3_1_366 56 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 114 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 114 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 114 207 3 18 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 114 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 53
  114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 114 207
  (Polychromatic418967fa.accept_10_2_4_7_1_352 52 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 114 207 3 17 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 114 207 (Polychromatic418967fa.accept_12_2_6_3_1_331 50 114 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 114 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 49
  114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 114 207 3 16 38 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 114 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 47 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 114 207 (Polychromatic418967fa.accept_11_2_4_9_1_484 46 114 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 114 207 3 15 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 114 207 (Polychromatic418967fa.accept_12_8_6_3_1_366
  44 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 114 207
  (Polychromatic418967fa.accept_10_3_4_7_1_353 43 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 207 3 14 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 114 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 114 207 (Polychromatic418967fa.accept_7_5_2_4_1_126
  40 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 114 207 3 13 38 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 114 207
  (Polychromatic418967fa.accept_12_2_6_3_1_331 38 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 114 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 114 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 114 207 3 12 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 114 207 (Polychromatic418967fa.accept_11_2_4_9_1_484
  35 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 114 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 34 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 114 207 3 11 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 114 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 32 114 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 114 207 (Polychromatic418967fa.accept_10_1_4_7_1_374
  31 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 114 207 3 10 38 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 114 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 114 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 114 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 114 207 3 9 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 114 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 26
  114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 207 3 8 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 114 207 (Polychromatic418967fa.accept_10_3_4_7_1_353 23 114 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 114 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 22 114
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 114 207 3 7 38 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 114 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 114 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 114 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 114 207 3 6 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 114 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 17
  114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 114 207
  (Polychromatic418967fa.accept_12_4_6_3_1_332 16 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 114 207 3 5 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 114 207 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 114 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 114 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 207 3 4 38 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 207
  (Polychromatic418967fa.accept_10_1_4_7_1_374 11 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 114 207 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 114 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 114 207 3 3 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 114 207 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 114 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 207
  (Polychromatic418967fa.accept_13_7_10_12_1_2047 7 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 114 207 3 2 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 114 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 114 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 114 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 114 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 114 207 3 1 38 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 114 207
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 114 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 114 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 114 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 114
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 113
  207 (Eq.refl Bool.true) (allA_succ_of_accept 94 113 207 (accept_3_4 94 113 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 113 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 93 113 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 113 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 92 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 113 207 (accept_3_4 91 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 113 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 113 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 89 113 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 113 207 (accept_3_4 88 113 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 113 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 87 113 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 113 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 113 207 (accept_3_4 85 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 113 207 (Polychromatic418967fa.accept_10_4_3_7_1_1110 84 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 113 207 (Polychromatic418967fa.accept_11_6_3_9_1_906 83 113 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 113 207 (accept_3_4 82 113 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 113 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 81 113
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 113 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 80 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 113 207 (accept_3_4 79 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 113 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 113 207 (Polychromatic418967fa.accept_17_9_11_3_1_2353 77 113 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 113 207 (accept_3_4 76 113 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 113 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 113 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 113 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 113 207 (accept_3_4 73 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 113 207 (Polychromatic418967fa.accept_11_6_3_9_1_906 72 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 113 207 (Polychromatic418967fa.accept_15_11_8_12_1_4437 71 113 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 207 (accept_3_4 70 113 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 113 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 69 113
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 113 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 113 207 (accept_3_4 67 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 113 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 113 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 65 113 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 207 (accept_3_4 64 113 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 113 207 (Polychromatic418967fa.accept_15_3_8_12_1_900 63 113
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 113 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 113 207 (accept_3_4 61 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 113 207 (Polychromatic418967fa.accept_13_8_9_12_1_2813 60 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 113 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 113 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 207 (accept_3_4 58 113 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 113 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 57 113 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 113 207 (accept_3_4 55 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 113 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 113 207 (Polychromatic418967fa.accept_16_5_1_15_1_3922 53 113 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 207 (accept_3_4 52 113 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 113 207 (Polychromatic418967fa.accept_18_15_5_9_1_5529 51 113
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 113 207 (accept_3_4 49 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 113 207 (Polychromatic418967fa.accept_15_3_8_12_1_900 48 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 113 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 113 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 207 (accept_3_4 46 113 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 113 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 113 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 113 207 (accept_3_4 43 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 113 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 113 207 (Polychromatic418967fa.accept_15_11_8_12_1_4437 41 113 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 207 (accept_3_4 40 113 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 113 207 (Polychromatic418967fa.accept_11_6_3_9_1_906 39 113
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 113 207 (accept_3_4 37 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 113 207 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 113 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 207 (accept_3_4 34 113 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 113 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 207 (accept_3_4 31 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 207 (Polychromatic418967fa.accept_13_3_9_12_1_2062 29 113 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 207 (accept_3_4 28 113 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 207 (Polychromatic418967fa.accept_16_11_1_15_1_1123 27 113
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 207 (accept_3_4 25 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 207 (Polychromatic418967fa.accept_13_10_9_12_1_2814 23 113 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 207 (accept_3_4 22 113 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 113
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 207 (accept_3_4 19 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 113 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 207 (accept_3_4 16 113 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 113 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 207 (accept_3_4 13 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 207 (Polychromatic418967fa.accept_15_11_8_12_1_4437 11 113 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 207 (accept_3_4 10 113 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 113 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 207 (accept_3_4 7 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 113 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 207 (accept_3_4 4 113 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 113 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 207 (accept_3_4 1 113 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 96 112
  207 (Eq.refl Bool.true) (allA_succ_of_accept 95 112 207 (accept_3_5 95 112 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 112 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 94 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 112 207
  (Polychromatic418967fa.accept_15_3_7_12_1_372 93 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 112 207 (accept_3_5 92 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 112 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 112 207 (Polychromatic418967fa.accept_12_6_4_3_1_361 90 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 112 207 (accept_3_5 89 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 112 207 (Polychromatic418967fa.accept_13_10_8_12_1_2032 88 112
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 112 207
  (Polychromatic418967fa.accept_13_9_8_12_1_2031 87 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 112 207 (accept_3_5 86 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 112 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 112 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 84 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 112 207 (accept_3_5 83 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 112 207 (Polychromatic418967fa.accept_13_4_8_12_1_3526 82 112
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 112 207
  (Polychromatic418967fa.accept_11_4_2_9_1_496 81 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 112 207 (accept_3_5 80 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 112 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 112 207 (Polychromatic418967fa.accept_12_6_4_3_1_361 78 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 112 207 (accept_3_5 77 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 112 207 (Polychromatic418967fa.accept_21_13_7_18_1_5966 76 112
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 112 207
  (Polychromatic418967fa.accept_10_5_2_7_1_345 75 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 112 207 (accept_3_5 74 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 112 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 112 207 (Polychromatic418967fa.accept_13_7_8_12_1_2810 72 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 112 207 (accept_3_5 71 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 112 207 (Polychromatic418967fa.accept_11_4_2_9_1_496 70 112
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 112 207
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 69 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 112 207 (accept_3_5 68 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 112 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 112 207 (Polychromatic418967fa.accept_12_6_4_3_1_361 66 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 112 207 (accept_3_5 65 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 112 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 64 112
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 112 207
  (Polychromatic418967fa.accept_15_3_7_12_1_372 63 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 112 207 (accept_3_5 62 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 112 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 112 207 (Polychromatic418967fa.accept_17_9_10_3_1_3423 60 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 112 207 (accept_3_5 59 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 112 207 (Polychromatic418967fa.accept_17_7_10_3_1_1421 58 112
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 112 207
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 57 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 112 207 (accept_3_5 56 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 112 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 112 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 54 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 112 207 (accept_3_5 53 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 112 207 (Polychromatic418967fa.accept_21_10_7_18_1_12065 52
  112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 112 207
  (Polychromatic418967fa.accept_11_7_2_9_1_480 51 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 112 207 (accept_3_5 50 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 112 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 112 207 (Polychromatic418967fa.accept_11_4_2_9_1_496 48 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 112 207 (accept_3_5 47 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 112 207 (Polychromatic418967fa.accept_13_7_8_12_1_2810 46 112
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 112 207
  (Polychromatic418967fa.accept_10_5_2_7_1_345 45 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 112 207 (accept_3_5 44 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 112 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 112 207 (Polychromatic418967fa.accept_12_6_4_3_1_361 42 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 112 207 (accept_3_5 41 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 112 207 (Polychromatic418967fa.accept_11_7_2_9_1_480 40 112
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 112 207
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 39 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 112 207 (accept_3_5 38 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 112 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 112 207 (Polychromatic418967fa.accept_13_10_8_12_1_2032 36 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 112 207 (accept_3_5 35 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 112 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 34 112
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 112 207
  (Polychromatic418967fa.accept_13_7_8_12_1_2810 33 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 112 207 (accept_3_5 32 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 112 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 112 207 (Polychromatic418967fa.accept_12_6_4_3_1_361 30 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 112 207 (accept_3_5 29 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 112 207 (Polychromatic418967fa.accept_17_11_10_3_1_2364 28 112
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 112 207
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 112 207 (accept_3_5 26 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 112 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 112 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 112 207 (accept_3_5 23 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 112 207 (Polychromatic418967fa.accept_13_9_8_12_1_2031 22 112
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 112 207
  (Polychromatic418967fa.accept_15_6_7_12_1_869 21 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 112 207 (accept_3_5 20 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 112 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 112 207 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 112 207 (accept_3_5 17 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 112 207 (Polychromatic418967fa.accept_22_16_2_9_1_12064 16 112
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 112 207
  (Polychromatic418967fa.accept_10_5_2_7_1_345 15 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 112 207 (accept_3_5 14 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 112 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 112 207 (Polychromatic418967fa.accept_18_12_4_9_1_5452 12 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 112 207 (accept_3_5 11 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 112 207 (Polychromatic418967fa.accept_13_10_8_12_1_2032 10 112
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 112 207
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 112 207 (accept_3_5 8 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  112 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 112 207 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 112 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 112 207 (accept_3_5 5 112 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 112 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 112 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 112 207
  (Polychromatic418967fa.accept_15_3_7_12_1_372 3 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 112 207 (accept_3_5 2 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  112 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 112 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 112
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 97 111
  207 (Eq.refl Bool.true) (allA_succ_of_gcd 96 111 207 3 32 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 111 207 (Polychromatic418967fa.accept_13_4_7_12_1_2823 95 111
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 111 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 94 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 111 207 3 31 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 111 207 (Polychromatic418967fa.accept_15_2_6_12_1_1613 92 111 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 207
  (Polychromatic418967fa.accept_17_6_9_3_1_704 91 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 111 207 3 30 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 111 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 89 111 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 111 207
  (Polychromatic418967fa.accept_13_10_7_12_1_2782 88 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 87 111 207 3 29 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 86 111 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 86 111 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 207
  (Polychromatic418967fa.accept_15_10_6_12_1_1645 85 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 111 207 3 28 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 111 207 (Polychromatic418967fa.accept_13_5_7_12_1_2757 83 111 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 111 207
  (Polychromatic418967fa.accept_7_5_6_4_1_117 82 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 111 207 3 27 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 111 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 80 111 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 79
  111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 111 207 3 26 37 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 111 207
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 77 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 111 207 (Polychromatic418967fa.accept_10_6_1_7_1_342 76 111 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 111 207 3 25 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 111 207 (Polychromatic418967fa.accept_10_4_1_7_1_371
  74 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 73 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 111 207 3 24 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 111 207 (Polychromatic418967fa.accept_13_6_7_12_1_3504 71 111 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 111 207
  (Polychromatic418967fa.accept_13_5_7_12_1_2757 70 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 111 207 3 23 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 111 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 68 111 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 207
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 67 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 111 207 3 22 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 111 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 65 111 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 111 207 (Polychromatic418967fa.accept_10_4_1_7_1_371
  64 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 111 207 3 21 37 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 111 207
  (Polychromatic418967fa.accept_13_10_7_12_1_2782 62 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 111 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 111 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 111 207 3 20 37 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 111 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 111 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 111 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 111 207 3 19 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 111 207 (Polychromatic418967fa.accept_10_6_1_7_1_342
  56 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 207
  (Polychromatic418967fa.accept_15_10_6_12_1_1645 55 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 111 207 3 18 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 111 207 (Polychromatic418967fa.accept_21_11_6_18_1_4450 53 111 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 52 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 111 207 3 17 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 111 207 (Polychromatic418967fa.accept_13_11_7_12_1_2758 50 111 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 207
  (Polychromatic418967fa.accept_13_10_7_12_1_2782 49 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 111 207 3 16 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 111 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 111 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 207
  (Polychromatic418967fa.accept_10_6_1_7_1_342 46 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 111 207 3 15 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 111 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 111 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 207
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 43 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 111 207 3 14 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 111 207 (Polychromatic418967fa.accept_19_3_16_17_1_3826 41 111 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 207
  (Polychromatic418967fa.accept_7_5_6_4_1_117 40 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 111 207 3 13 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 111 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 111 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 37
  111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 111 207 3 12 37 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 111 207
  (Polychromatic418967fa.accept_15_5_6_12_1_916 35 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 207 (Polychromatic418967fa.accept_10_4_1_7_1_371 34 111 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 111 207 3 11 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 111 207 (Polychromatic418967fa.accept_11_10_1_9_1_2060
  32 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 111 207 3 10 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 111 207 (Polychromatic418967fa.accept_25_4_11_7_1_12095 29 111 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 207
  (Polychromatic418967fa.accept_17_11_9_3_1_1463 28 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 111 207 3 9 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 111 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 111 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 207 (Polychromatic418967fa.accept_15_10_6_12_1_1645 25 111
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 111 207 3 8 37 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 111 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 207 (Polychromatic418967fa.accept_15_7_6_12_1_1614 22 111 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 111 207 3 7 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 111 207 (Polychromatic418967fa.accept_15_5_6_12_1_916
  20 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 207
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 111 207 3 6 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 111 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 111 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 111 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 111 207 3 5 37 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 111 207
  (Polychromatic418967fa.accept_10_4_1_7_1_371 14 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 111 207 (Polychromatic418967fa.accept_18_13_3_9_1_4233 13 111 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 111 207 3 4 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 111 207
  (Polychromatic418967fa.accept_13_11_7_12_1_2758 11 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 111 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 111 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 111 207 3 3 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 111 207 (Polychromatic418967fa.accept_13_8_7_12_1_3637
  8 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 207
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 7 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 111 207 3 2 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 111 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 111 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 207 (Polychromatic418967fa.accept_10_4_1_7_1_371 4 111 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 111 207 3 1 37 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 111 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 111 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 207 (Polychromatic418967fa.accept_17_1_9_3_1_7161 1 111 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 111
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  110 207 (Eq.refl Bool.true) (allA_succ_of_accept 97 110 207 (accept_3_4 97 110 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 110 207 (Polychromatic418967fa.accept_13_5_6_12_1_2750 96 110 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 110 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 95 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 110 207 (accept_3_4 94 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 110 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 110 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 92 110 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 110 207 (accept_3_4 91 110 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 110 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 90 110 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 110 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 110 207 (accept_3_4 88 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 110 207 (Polychromatic418967fa.accept_16_7_14_15_1_2932 87 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 110 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 86 110 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 110 207 (accept_3_4 85 110 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 110 207 (Polychromatic418967fa.accept_15_9_5_12_1_1640 84 110 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 110 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 110 207 (accept_3_4 82 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 110 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 110 207 (Polychromatic418967fa.accept_13_2_6_12_1_1334 80 110 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 110 207 (accept_3_4 79 110 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 110 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 78 110 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 110 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 110 207 (accept_3_4 76 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 110 207 (Polychromatic418967fa.accept_13_10_6_12_1_2780 75 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 110 207 (Polychromatic418967fa.accept_16_10_14_15_1_2933 74 110 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 110 207 (accept_3_4 73 110 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 110 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 110 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 110 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 110 207 (accept_3_4 70 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 110 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 110 207 (Polychromatic418967fa.accept_15_8_5_12_1_4453 68 110 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 110 207 (accept_3_4 67 110 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 110 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 66 110
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 110 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 110 207 (accept_3_4 64 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 110 207 (Polychromatic418967fa.accept_17_12_8_3_1_4646 63 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 110 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 62 110 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 110 207 (accept_3_4 61 110 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 110 207 (Polychromatic418967fa.accept_18_6_2_9_1_3056 60 110 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 110 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 110 207 (accept_3_4 58 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 110 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 110 207 (Polychromatic418967fa.accept_17_5_8_3_1_1419 56 110 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 110 207 (accept_3_4 55 110 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 110 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 54 110
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 110 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 110 207 (accept_3_4 52 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 110 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 110 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 50 110 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 110 207 (accept_3_4 49 110 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 110 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 110 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 110 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 110 207 (accept_3_4 46 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 110 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 110 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 110 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 110 207 (accept_3_4 43 110 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 110 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 110 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 110 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 110 207 (accept_3_4 40 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 110 207 (Polychromatic418967fa.accept_15_9_5_12_1_1640 39 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 110 207 (Polychromatic418967fa.accept_15_8_5_12_1_4453 38 110 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 110 207 (accept_3_4 37 110 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 110 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 110 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 110 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 110 207 (accept_3_4 34 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 110 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 110 207 (Polychromatic418967fa.accept_15_2_5_12_1_369 32 110 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 110 207 (accept_3_4 31 110 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 110 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 110 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 110 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 110 207 (accept_3_4 28 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 110 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 110 207 (Polychromatic418967fa.accept_16_10_14_15_1_2933 26 110 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 110 207 (accept_3_4 25 110 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 110 207 (Polychromatic418967fa.accept_15_9_5_12_1_1640 24 110
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 110 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 110 207 (accept_3_4 22 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 110 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 110 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 110 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 110 207 (accept_3_4 19 110 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 110 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 110 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 110 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 110 207 (accept_3_4 16 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 110 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 110 207 (Polychromatic418967fa.accept_19_14_15_17_1_3877 14 110 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 110 207 (accept_3_4 13 110 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 110 207 (Polychromatic418967fa.accept_17_12_8_3_1_4646 12 110
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 110 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 110 207 (accept_3_4 10 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  110 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 110 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 110 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 110 207 (accept_3_4 7 110 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 110 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 110 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 110 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 110 207 (accept_3_4 4 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  110 207 (Polychromatic418967fa.accept_18_3_2_9_1_1013 3 110 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 110 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 110 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 110 207 (accept_3_4 1 110 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 110
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 99
  109 207 (Eq.refl Bool.true) (allA_succ_of_accept 98 109 207 (accept_3_5 98 109 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 109 207 (Polychromatic418967fa.accept_13_6_5_12_1_307 97 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 109 207
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 96 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 109 207 (accept_3_5 95 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 109 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 109 207 (Polychromatic418967fa.accept_12_9_1_3_1_350 93 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 109 207 (accept_3_5 92 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 109 207 (Polychromatic418967fa.accept_15_1_4_12_1_2401 91 109
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 109 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 90 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 109 207 (accept_3_5 89 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 109 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 109 207 (Polychromatic418967fa.accept_19_11_14_17_1_6607 87 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 109 207 (accept_3_5 86 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 109 207 (Polychromatic418967fa.accept_11_8_10_9_1_1401 85 109
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 109 207
  (Polychromatic418967fa.accept_13_6_5_12_1_307 84 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 109 207 (accept_3_5 83 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 109 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 109 207 (Polychromatic418967fa.accept_12_9_1_3_1_350 81 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 109 207 (accept_3_5 80 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 109 207 (Polychromatic418967fa.accept_13_1_5_12_1_306 79 109
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 109 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 109 207 (accept_3_5 77 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 109 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 109 207 (Polychromatic418967fa.accept_18_3_1_9_1_1929 75 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 109 207 (accept_3_5 74 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 109 207 (Polychromatic418967fa.accept_13_8_5_12_1_2755 73 109
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 109 207
  (Polychromatic418967fa.accept_10_2_9_7_1_720 72 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 109 207 (accept_3_5 71 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 109 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 109 207 (Polychromatic418967fa.accept_12_9_1_3_1_350 69 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 109 207 (accept_3_5 68 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 109 207 (Polychromatic418967fa.accept_11_1_10_9_1_871 67 109
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 109 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 109 207 (accept_3_5 65 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 109 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 109 207 (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 109 207 (accept_3_5 62 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 109 207 (Polychromatic418967fa.accept_15_1_4_12_1_2401 61 109
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 109 207
  (Polychromatic418967fa.accept_13_8_5_12_1_2755 60 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 109 207 (accept_3_5 59 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 109 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 109 207 (Polychromatic418967fa.accept_12_9_1_3_1_350 57 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 109 207 (accept_3_5 56 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 109 207 (Polychromatic418967fa.accept_17_4_7_3_1_1417 55 109
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 109 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 109 207 (accept_3_5 53 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 109 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 109 207 (Polychromatic418967fa.accept_16_3_13_15_1_1913 51 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 109 207 (accept_3_5 50 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 109 207 (Polychromatic418967fa.accept_19_11_14_17_1_6607 49
  109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 109 207
  (Polychromatic418967fa.accept_10_8_9_7_1_1118 48 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 109 207 (accept_3_5 47 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 109 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 109 207 (Polychromatic418967fa.accept_11_1_10_9_1_871 45 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 109 207 (accept_3_5 44 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 109 207 (Polychromatic418967fa.accept_13_4_5_12_1_751 43 109
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 109 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 109 207 (accept_3_5 41 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 109 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 109 207 (Polychromatic418967fa.accept_15_9_4_12_1_1611 39 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 109 207 (accept_3_5 38 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 109 207 (Polychromatic418967fa.accept_15_7_4_12_1_2530 37 109
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 109 207
  (Polychromatic418967fa.accept_20_16_9_7_1_3402 36 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 109 207 (accept_3_5 35 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 109 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 109 207 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 109 207 (accept_3_5 32 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 109 207 (Polychromatic418967fa.accept_15_1_4_12_1_2401 31 109
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 109 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 109 207 (accept_3_5 29 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 109 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 109 207 (Polychromatic418967fa.accept_13_1_5_12_1_306 27 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 109 207 (accept_3_5 26 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 109 207 (Polychromatic418967fa.accept_20_5_9_7_1_10766 25 109
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 109 207
  (Polychromatic418967fa.accept_15_9_4_12_1_1611 24 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 109 207 (accept_3_5 23 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 109 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 109 207 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 207 (accept_3_5 20 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 109 207 (Polychromatic418967fa.accept_11_8_10_9_1_1401 19 109
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 109 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 109 207 (accept_3_5 17 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 109 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 109 207 (Polychromatic418967fa.accept_13_2_5_12_1_2043 15 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 207 (accept_3_5 14 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 207 (Polychromatic418967fa.accept_21_13_4_18_1_7553 13 109
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 207
  (Polychromatic418967fa.accept_10_2_9_7_1_720 12 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 109 207 (accept_3_5 11 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 109 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 109 207 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 109 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 207 (accept_3_5 8 109 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 207 (Polychromatic418967fa.accept_13_7_5_12_1_1305 7 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 207 (accept_3_5 5 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 109 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 207 (Polychromatic418967fa.accept_16_3_13_15_1_1913 3 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 207 (accept_3_5 2 109 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 207 (Polychromatic418967fa.accept_11_1_10_9_1_871 1 109 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 100
  108 207 (Eq.refl Bool.true) (allA_succ_of_gcd 99 108 207 9 11 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 108 207 (Polychromatic418967fa.accept_13_7_4_12_1_1341 98 108
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 108 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 97 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 108 207 3 32 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 108 207 (Polychromatic418967fa.accept_10_5_8_7_1_2174 95 108 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 108 207
  (Polychromatic418967fa.accept_13_3_4_12_1_36 94 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 108 207 3 31 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 108 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 92 108 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 108 207 (Polychromatic418967fa.accept_8_3_4_7_1_475
  91 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 108 207 9 10 12 23
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 108 207
  (Polychromatic418967fa.accept_10_9_8_7_1_714 89 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 108 207 (Polychromatic418967fa.accept_15_13_3_12_1_1609 88 108 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 108 207 3 29 36 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 108 207
  (Polychromatic418967fa.accept_13_8_4_12_1_2753 86 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 108 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 85 108 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 108 207 3 28 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 108 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 83
  108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 108 207
  (Polychromatic418967fa.accept_15_7_3_12_1_365 82 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 108 207 9 9 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 80 108 207 (Polychromatic418967fa.accept_13_2_4_12_1_745 80 108 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 108 207 (Polychromatic418967fa.accept_10_9_8_7_1_714 79 108
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 108 207 3 26 36 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 108 207
  (Polychromatic418967fa.accept_14_7_10_11_1_8112 77 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 108 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 76 108 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 108 207 3 25 36 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 108 207
  (Polychromatic418967fa.accept_21_11_3_18_1_3068 74 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 108 207 (Polychromatic418967fa.accept_13_8_4_12_1_2753 73 108 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 108 207 9 8 12 23 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 108 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 71 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 108 207 (Polychromatic418967fa.accept_13_5_4_12_1_2058 70 108 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 108 207 3 23 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 108 207 (Polychromatic418967fa.accept_13_3_4_12_1_36
  68 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 108 207
  (Polychromatic418967fa.accept_8_3_4_7_1_475 67 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 108 207 3 22 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 207 (Polychromatic418967fa.accept_10_5_8_7_1_2174 65 108 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 108 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 64 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 108 207 9 7 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 108 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 62 108 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 108 207 (Polychromatic418967fa.accept_16_13_12_15_1_6290 61
  108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 108 207 3 20 36 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 108 207
  (Polychromatic418967fa.accept_8_3_4_7_1_475 59 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 108 207 (Polychromatic418967fa.accept_15_13_3_12_1_1609 58 108 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 108 207 3 19 36 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 108 207
  (Polychromatic418967fa.accept_16_8_12_15_1_2005 56 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 108 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 108 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 108 207 9 6 12 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 108 207
  (Polychromatic418967fa.accept_15_8_3_12_1_1657 53 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 108 207 (Polychromatic418967fa.accept_15_7_3_12_1_365 52 108 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 108 207 3 17 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 108 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 50
  108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 108 207
  (Polychromatic418967fa.accept_10_9_8_7_1_714 49 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 207 3 16 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 108 207 (Polychromatic418967fa.accept_13_8_4_12_1_2753 47 108 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 108 207
  (Polychromatic418967fa.accept_13_7_4_12_1_1341 46 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 108 207 9 5 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 108 207 (Polychromatic418967fa.accept_13_5_4_12_1_2058 44 108 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 108 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 108 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 108 207 3 14 36 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 108 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 108 207 (Polychromatic418967fa.accept_16_8_12_15_1_2005 40 108 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 108 207 3 13 36 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 108 207
  (Polychromatic418967fa.accept_15_8_3_12_1_1657 38 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 108 207 (Polychromatic418967fa.accept_13_11_4_12_1_3585 37 108 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 108 207 9 4 12 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 108 207
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 108 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 108 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 108 207 3 11 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 108 207 (Polychromatic418967fa.accept_15_2_3_12_1_891
  32 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 108 207
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 31 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 207 3 10 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 108 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 108 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 207 (Polychromatic418967fa.accept_13_2_4_12_1_745
  28 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 108 207 9 3 12 23
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 108 207
  (Polychromatic418967fa.accept_17_9_6_3_1_2398 26 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 108 207 (Polychromatic418967fa.accept_10_5_8_7_1_2174 25 108 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 108 207 3 8 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 108 207 (Polychromatic418967fa.accept_15_8_3_12_1_1657
  23 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 108 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 22 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 108 207 3 7 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 108 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 108 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 108 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 108 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 108 207 9 2 12 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 108 207
  (Polychromatic418967fa.accept_15_2_3_12_1_891 17 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 108 207 (Polychromatic418967fa.accept_13_3_4_12_1_36 16 108 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 108 207 3 5 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 108 207 (Polychromatic418967fa.accept_17_14_6_3_1_2362
  14 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 108 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 108 207 3 4 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 108 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 108 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 207 (Polychromatic418967fa.accept_20_10_8_7_1_7834 10 108
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 108 207 9 1 12 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 108 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 108 207 (Polychromatic418967fa.accept_13_7_4_12_1_1341 7 108 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 207 3 2 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 207 (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 108 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 207
  (Polychromatic418967fa.accept_16_4_12_15_1_6289 4 108 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 108 207 3 1 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 108 207 (Polychromatic418967fa.accept_13_2_4_12_1_745 2 108 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 108 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 107 207 (Eq.refl Bool.true) (allA_succ_of_accept 100 107 207 (accept_3_4 100 107 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 107 207 (Polychromatic418967fa.accept_16_3_11_15_1_1963 99 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 107 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 98 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 107 207 (accept_3_4 97 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 107 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 96 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 107 207 (Polychromatic418967fa.accept_13_4_3_12_1_2066 95 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 107 207 (accept_3_4 94 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 107 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 93 107
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 107 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 92 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 107 207 (accept_3_4 91 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 107 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 90 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 107 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 89 107 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 107 207 (accept_3_4 88 107 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 107 207 (Polychromatic418967fa.accept_11_10_8_9_1_492 87 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 107 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 86 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 107 207 (accept_3_4 85 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 107 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 84 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 107 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 83 107 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 107 207 (accept_3_4 82 107 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 107 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 81 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 107 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 80 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 107 207 (accept_3_4 79 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 107 207 (Polychromatic418967fa.accept_15_3_2_12_1_2469 78 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 107 207 (Polychromatic418967fa.accept_22_11_19_9_1_10608 77 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 207 (accept_3_4 76 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 107 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 75 107 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 74 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 107 207 (accept_3_4 73 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 107 207 (Polychromatic418967fa.accept_14_2_9_11_1_3054 72 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 107 207 (Polychromatic418967fa.accept_16_7_11_15_1_2929 71 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 207 (accept_3_4 70 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 107 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 107 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 107 207 (accept_3_4 67 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 107 207 (Polychromatic418967fa.accept_15_6_2_12_1_885 66 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 107 207 (Polychromatic418967fa.accept_11_10_8_9_1_492 65 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 207 (accept_3_4 64 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 207 (Polychromatic418967fa.accept_15_3_2_12_1_2469 63 107
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 62 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 107 207 (accept_3_4 61 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 107 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 107 207 (Polychromatic418967fa.accept_15_14_2_12_1_2472 59 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 207 (accept_3_4 58 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 107 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 57 107
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 207 (accept_3_4 55 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 207 (Polychromatic418967fa.accept_17_2_5_3_1_1416 53 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 207 (accept_3_4 52 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 207 (Polychromatic418967fa.accept_15_6_2_12_1_885 51 107
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 207 (accept_3_4 49 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 107 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 207 (accept_3_4 46 107 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 207 (accept_3_4 43 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 207 (Polychromatic418967fa.accept_16_10_11_15_1_6302 42 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 41 107 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 207 (accept_3_4 40 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 207 (Polychromatic418967fa.accept_16_7_11_15_1_2929 39 107
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 207 (accept_3_4 37 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 207 (Polychromatic418967fa.accept_13_9_3_12_1_2025 35 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 207 (accept_3_4 34 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 107 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 107 207 (accept_3_4 31 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 107 207 (Polychromatic418967fa.accept_13_4_3_12_1_2066 30 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 107 207 (Polychromatic418967fa.accept_15_14_2_12_1_2472 29 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 207 (accept_3_4 28 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 107 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 207 (accept_3_4 25 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 207 (Polychromatic418967fa.accept_19_5_12_17_1_8089 24 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 207 (Polychromatic418967fa.accept_16_7_11_15_1_2929 23 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 207 (accept_3_4 22 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 207 (Polychromatic418967fa.accept_11_10_8_9_1_492 21 107
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 207 (accept_3_4 19 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 207 (Polychromatic418967fa.accept_15_3_2_12_1_2469 18 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 207 (Polychromatic418967fa.accept_13_4_3_12_1_2066 17 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 207 (accept_3_4 16 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 207 (Polychromatic418967fa.accept_13_2_3_12_1_735 15 107
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 207 (accept_3_4 13 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 207 (Polychromatic418967fa.accept_22_11_19_9_1_10608 11 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 207 (accept_3_4 10 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 107 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 207 (accept_3_4 7 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 107 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 207 (accept_3_4 4 107 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 207 (Polychromatic418967fa.accept_15_3_2_12_1_2469 3 107 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 207 (accept_3_4 1 107 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  102 106 207 (Eq.refl Bool.true) (allA_succ_of_accept 101 106 207 (accept_3_5 101 106 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 106 207 (Polychromatic418967fa.accept_19_5_11_17_1_6536 100 106 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 106 207
  (Polychromatic418967fa.accept_19_4_11_17_1_9505 99 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 106 207 (accept_3_5 98 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 106 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 106 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 106 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 96 106 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 106 207 (accept_3_5 95 106 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 106 207 (Polychromatic418967fa.accept_7_3_1_4_1_121
  94 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 106 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 106 207 (accept_3_5 92 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 106 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 106 207 (Polychromatic418967fa.accept_11_2_7_9_1_890 90 106 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 106 207 (accept_3_5 89 106 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 106 207 (Polychromatic418967fa.accept_13_10_2_12_1_1332 88 106
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 106 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 87 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 106 207 (accept_3_5 86 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 106 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 106 207 (Polychromatic418967fa.accept_13_6_2_12_1_2802 84 106 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 106 207 (accept_3_5 83 106 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 106 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 82 106 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 106 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 106 207 (accept_3_5 80 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 106 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 106 207 (Polychromatic418967fa.accept_12_6_10_3_1_1313 78 106 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 106 207 (accept_3_5 77 106 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 106 207 (Polychromatic418967fa.accept_20_16_6_7_1_10779 76 106
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 106 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 75 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 106 207 (accept_3_5 74 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 106 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 106 207 (Polychromatic418967fa.accept_20_12_6_7_1_7875 72 106 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 106 207 (accept_3_5 71 106 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 106 207 (Polychromatic418967fa.accept_13_5_2_12_1_1301 70 106
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 106 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 106 207 (accept_3_5 68 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 106 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 106 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 106 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 106 207 (accept_3_5 65 106 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 106 207 (Polychromatic418967fa.accept_15_4_1_12_1_914 64 106 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 106 207
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 63 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 106 207 (accept_3_5 62 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 106 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 106 207 (Polychromatic418967fa.accept_11_5_7_9_1_2696 60 106 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 106 207 (accept_3_5 59 106 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 106 207 (Polychromatic418967fa.accept_13_6_2_12_1_2802 58 106
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 106 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 106 207 (accept_3_5 56 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 106 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 106 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 106 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 106 207 (accept_3_5 53 106 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 106 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 106 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 106 207
  (Polychromatic418967fa.accept_10_1_6_7_1_710 51 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 106 207 (accept_3_5 50 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 106 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 106 207 (Polychromatic418967fa.accept_18_12_16_9_1_4198 48 106 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 106 207 (accept_3_5 47 106 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 106 207 (Polychromatic418967fa.accept_11_2_7_9_1_890 46 106
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 106 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 106 207 (accept_3_5 44 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 106 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 106 207 (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 106 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 106 207 (accept_3_5 41 106 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 106 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 106 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 106 207
  (Polychromatic418967fa.accept_20_19_6_7_1_9289 39 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 106 207 (accept_3_5 38 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 106 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 106 207 (Polychromatic418967fa.accept_13_10_2_12_1_1332 36 106 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 106 207 (accept_3_5 35 106 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 106 207 (Polychromatic418967fa.accept_15_4_1_12_1_914 34 106
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 106 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 106 207 (accept_3_5 32 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 106 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 106 207 (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 106 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 106 207 (accept_3_5 29 106 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 106 207 (Polychromatic418967fa.accept_15_13_1_12_1_1638 28 106
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 106 207
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 106 207 (accept_3_5 26 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 106 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 106 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 106 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 106 207 (accept_3_5 23 106 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 106 207 (Polychromatic418967fa.accept_25_22_6_7_1_12094 22 106 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 106 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 106 207 (accept_3_5 20 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 106 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 106 207 (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 106 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 106 207 (accept_3_5 17 106 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 106 207 (Polychromatic418967fa.accept_11_5_7_9_1_2696 16 106
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 106 207
  (Polychromatic418967fa.accept_18_15_16_9_1_4299 15 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 106 207 (accept_3_5 14 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 106 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 106 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 106 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 106 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 106 207 (accept_3_5 11 106 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 106 207 (Polychromatic418967fa.accept_7_3_1_4_1_121
  10 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 106 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 106 207 (accept_3_5 8 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  106 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 106 207 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 106 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 106 207 (accept_3_5 5 106 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 106 207 (Polychromatic418967fa.accept_13_4_2_12_1_2800 4 106
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 106 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 106 207 (accept_3_5 2 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  106 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 106 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 106
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  103 105 207 (Eq.refl Bool.true) (allA_succ_of_gcd 102 105 207 3 34 35 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 105 207 (Polychromatic418967fa.accept_12_5_9_3_1_85
  101 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 105 207
  (Polychromatic418967fa.accept_18_10_15_9_1_1054 100 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 99 105 207 3 33 35 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 98 105 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 105 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 105 207
  (Polychromatic418967fa.accept_12_1_9_3_1_370 97 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 105 207 3 32 35 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 105 207 (Polychromatic418967fa.accept_12_11_9_3_1_792 95 105 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 105 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 94 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 105 207 3 31 35 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 105 207 (Polychromatic418967fa.accept_10_2_5_7_1_1124 92 105 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 105 207
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 91 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 105 207 3 30 35 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 105 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 89 105 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 105 207 (Polychromatic418967fa.accept_10_8_5_7_1_358
  88 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 105 207 3 29 35 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 105 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 105 207 (Polychromatic418967fa.accept_12_1_9_3_1_370 85 105 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 105 207 3 28 35 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 105 207 (Polychromatic418967fa.accept_10_3_5_7_1_330
  83 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 105 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 82 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 105 207 3 27 35 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 105 207 (Polychromatic418967fa.accept_11_3_6_9_1_1378 80 105 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 207
  (Polychromatic418967fa.accept_12_7_9_3_1_767 79 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 105 207 3 26 35 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 105 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 77 105 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 105 207
  (Polychromatic418967fa.accept_13_11_1_12_1_742 76 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 105 207 3 25 35 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 105 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 105 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 207 (Polychromatic418967fa.accept_10_3_5_7_1_330
  73 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 105 207 3 24 35 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 105 207
  (Polychromatic418967fa.accept_12_11_9_3_1_792 71 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 105 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 105 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 105 207 3 23 35 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 105 207 (Polychromatic418967fa.accept_10_8_5_7_1_358
  68 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 207
  (Polychromatic418967fa.accept_12_7_9_3_1_767 67 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 105 207 3 22 35 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 105 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 65 105 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 105 207
  (Polychromatic418967fa.accept_18_10_15_9_1_1054 64 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 105 207 3 21 35 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 105 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 105 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 207
  (Polychromatic418967fa.accept_12_1_9_3_1_370 61 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 105 207 3 20 35 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 105 207 (Polychromatic418967fa.accept_12_11_9_3_1_792 59 105 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 105 207 3 19 35 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 105 207 (Polychromatic418967fa.accept_16_8_9_15_1_5112 56 105 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 207
  (Polychromatic418967fa.accept_12_7_9_3_1_767 55 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 105 207 3 18 35 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 105 207 (Polychromatic418967fa.accept_10_3_5_7_1_330 53 105 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 207 (Polychromatic418967fa.accept_10_2_5_7_1_1124
  52 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 105 207 3 17 35 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 105 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 105 207 (Polychromatic418967fa.accept_12_1_9_3_1_370 49 105 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 105 207 3 16 35 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 105 207 (Polychromatic418967fa.accept_11_3_6_9_1_1378
  47 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 105 207 3 15 35 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 105 207 (Polychromatic418967fa.accept_13_5_1_12_1_740 44 105 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 207
  (Polychromatic418967fa.accept_10_3_5_7_1_330 43 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 105 207 3 14 35 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 105 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 41 105 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 105 207
  (Polychromatic418967fa.accept_16_8_9_15_1_5112 40 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 105 207 3 13 35 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 105 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 105 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 207 (Polychromatic418967fa.accept_12_1_9_3_1_370
  37 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 105 207 3 12 35 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 105 207
  (Polychromatic418967fa.accept_12_11_9_3_1_792 35 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 105 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 105 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 105 207 3 11 35 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 105 207 (Polychromatic418967fa.accept_10_2_5_7_1_1124
  32 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 207
  (Polychromatic418967fa.accept_12_7_9_3_1_767 31 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 105 207 3 10 35 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 105 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 29 105 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 207 (Polychromatic418967fa.accept_10_8_5_7_1_358
  28 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 105 207 3 9 35 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 105 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 105 207 (Polychromatic418967fa.accept_11_3_6_9_1_1378 25 105 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 105 207 3 8 35 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 105 207 (Polychromatic418967fa.accept_10_3_5_7_1_330
  23 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 105 207 3 7 35 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 105 207 (Polychromatic418967fa.accept_19_1_10_17_1_5188 20 105 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 207 (Polychromatic418967fa.accept_12_7_9_3_1_767
  19 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 105 207 3 6 35 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 105 207
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 207 (Polychromatic418967fa.accept_18_16_15_9_1_6852 16 105 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 105 207 3 5 35 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 105 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 105 207 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 105 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 105 207 3 4 35 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 105 207 (Polychromatic418967fa.accept_12_11_9_3_1_792
  11 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 105 207 3 3 35 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 105 207 (Polychromatic418967fa.accept_10_8_5_7_1_358 8 105 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 105 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 105 207 3 2 35 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 105 207
  (Polychromatic418967fa.accept_12_5_9_3_1_85 5 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 207 (Polychromatic418967fa.accept_14_4_7_11_1_790 4 105 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 105 207 3 1 35 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 105 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 105 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 207
  (Polychromatic418967fa.accept_12_1_9_3_1_370 1 105 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 105
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  104 207 (allA_succ_of_accept 103 104 207 (accept_3_4 103 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 104 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 102 104 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 104 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 101 104
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 104 207 (accept_3_4 100 104
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 104 207
  (Polychromatic418967fa.accept_15_9_14_12_1_913 99 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 104 207 (Polychromatic418967fa.accept_21_14_20_18_1_9174 98 104 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 104 207 (accept_3_4 97 104 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 104 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 96 104 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 104 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 95 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 104 207 (accept_3_4 94 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 104 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 93 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 104 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 92 104 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 104 207 (accept_3_4 91 104 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 104 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 90 104 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 104 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 89 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 104 207 (accept_3_4 88 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 104 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 87 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 104 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 86 104 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 104 207 (accept_3_4 85 104 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 104 207 (Polychromatic418967fa.accept_11_7_5_9_1_884 84 104 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 104 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 104 207 (accept_3_4 82 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 104 207 (Polychromatic418967fa.accept_10_1_4_7_1_374 81 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 104 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 80 104 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 104 207 (accept_3_4 79 104 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 104 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 78 104 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 104 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 77 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 104 207 (accept_3_4 76 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 104 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 104 207 (Polychromatic418967fa.accept_21_11_20_18_1_7656 74 104 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 104 207 (accept_3_4 73 104 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 104 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 104 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 104 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 104 207 (accept_3_4 70 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 104 207 (Polychromatic418967fa.accept_15_9_14_12_1_913 69 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 104 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 68 104 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 104 207 (accept_3_4 67 104 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 104 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 104 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 104 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 65 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 104 207 (accept_3_4 64 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 104 207 (Polychromatic418967fa.accept_10_3_4_7_1_353 63 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 104 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 62 104 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 104 207 (accept_3_4 61 104 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 104 207 (Polychromatic418967fa.accept_16_12_8_15_1_5119 60 104
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 104 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 104 207 (accept_3_4 58 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 104 207 (Polychromatic418967fa.accept_16_9_8_15_1_5095 57 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 104 207 (Polychromatic418967fa.accept_15_11_14_12_1_2458 56 104 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 104 207 (accept_3_4 55 104 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 104 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 104 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 104 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 104 207 (accept_3_4 52 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 104 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 104 207 (Polychromatic418967fa.accept_22_6_16_9_1_12093 50 104 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 104 207 (accept_3_4 49 104 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 104 207 (Polychromatic418967fa.accept_17_14_2_3_1_7172 48 104
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 104 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 104 207 (accept_3_4 46 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 104 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 104 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 104 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 104 207 (accept_3_4 43 104 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 104 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 104 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 104 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 104 207 (accept_3_4 40 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 104 207 (Polychromatic418967fa.accept_15_9_14_12_1_913 39 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 104 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 104 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 104 207 (accept_3_4 37 104 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 104 207 (Polychromatic418967fa.accept_16_4_8_15_1_1113 36 104 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 104 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 104 207 (accept_3_4 34 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 104 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 104 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 32 104 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 104 207 (accept_3_4 31 104 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 104 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 104 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 104 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 104 207 (accept_3_4 28 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 104 207 (Polychromatic418967fa.accept_19_8_9_17_1_5151 27 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 104 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 104 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 104 207 (accept_3_4 25 104 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 104 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 104 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 104 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 104 207 (accept_3_4 22 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 104 207 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 104 207 (Polychromatic418967fa.accept_16_4_8_15_1_1113 20 104 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 104 207 (accept_3_4 19 104 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 104 207 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 104
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 104 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 104 207 (accept_3_4 16 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 104 207 (Polychromatic418967fa.accept_21_15_20_18_1_5985 15 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 14 104 207 (Polychromatic418967fa.accept_17_14_2_3_1_7172 14 104 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 104 207 (accept_3_4 13 104 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 104 207 (Polychromatic418967fa.accept_7_5_6_4_1_117
  12 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 104 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 104 207 (accept_3_4 10 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  104 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 104 207 (Polychromatic418967fa.accept_19_8_9_17_1_5151 8 104 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 104 207 (accept_3_4 7 104 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 104 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 104 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 104 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 104 207 (accept_3_4 4 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  104 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 104 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 104 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 104 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 104 207 (accept_3_4 1 104 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 104
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  103 207 (allA_succ_of_accept 102 103 207 (Polychromatic418967fa.accept_16_6_7_15_1_1942 102 103 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 103 207 (accept_3_5 101 103 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 103 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 100 103
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 103 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 99 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 103 207 (accept_3_5 98 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 103 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 97 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 103 207 (Polychromatic418967fa.accept_10_6_3_7_1_2197 96 103 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 103 207 (accept_3_5 95 103 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 103 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 94 103 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 103 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 93 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 103 207 (accept_3_5 92 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 103 207 (Polychromatic418967fa.accept_15_1_13_12_1_347 91 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 103 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 90 103 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 103 207 (accept_3_5 89 103 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 103 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 103 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 103 207
  (Polychromatic418967fa.accept_17_2_1_3_1_2357 87 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 103 207 (accept_3_5 86 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 103 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 85 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 103 207 (Polychromatic418967fa.accept_10_4_3_7_1_1110 84 103 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 103 207 (accept_3_5 83 103 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 103 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 103 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 103 207
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 81 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 103 207 (accept_3_5 80 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 103 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 79 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 103 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 78 103 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 103 207 (accept_3_5 77 103 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 103 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 103 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 103 207
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 75 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 103 207 (accept_3_5 74 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 103 207 (Polychromatic418967fa.accept_19_16_8_17_1_5148 73 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 103 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 103 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 103 207 (accept_3_5 71 103 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 103 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 103 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 103 207
  (Polychromatic418967fa.accept_7_6_5_4_1_297 69 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 103 207 (accept_3_5 68 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 103 207 (Polychromatic418967fa.accept_16_3_7_15_1_1130 67 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 103 207 (Polychromatic418967fa.accept_10_6_3_7_1_2197 66 103 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 103 207 (accept_3_5 65 103 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 103 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 103 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 103 207
  (Polychromatic418967fa.accept_15_3_13_12_1_348 63 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 103 207 (accept_3_5 62 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 103 207 (Polychromatic418967fa.accept_15_1_13_12_1_347 61 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 103 207 (Polychromatic418967fa.accept_17_9_1_3_1_4626 60 103 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 103 207 (accept_3_5 59 103 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 103 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 103 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 103 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 57 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 103 207 (accept_3_5 56 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 103 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 103 207 (Polychromatic418967fa.accept_10_4_3_7_1_1110 54 103 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 207 (accept_3_5 53 103 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 103 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 103 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 103 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 103 207 (accept_3_5 50 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 103 207 (Polychromatic418967fa.accept_17_15_1_3_1_1488 49 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 103 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 103 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 103 207 (accept_3_5 47 103 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 103 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 103 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 207
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 103 207 (accept_3_5 44 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 103 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 103 207 (Polychromatic418967fa.accept_18_6_13_9_1_4218 42 103 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 207 (accept_3_5 41 103 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 103 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 207
  (Polychromatic418967fa.accept_18_3_13_9_1_4260 39 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 207 (accept_3_5 38 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 103 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 207 (accept_3_5 35 103 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 103 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 207
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 207 (accept_3_5 32 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 207 (Polychromatic418967fa.accept_15_1_13_12_1_347 31 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 103 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 207 (accept_3_5 29 103 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 103 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 207
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 207 (accept_3_5 26 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 207 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 103 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 207 (accept_3_5 23 103 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 103 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 207
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 207 (accept_3_5 20 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 207 (Polychromatic418967fa.accept_16_3_7_15_1_1130 19 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 207 (Polychromatic418967fa.accept_15_3_13_12_1_348 18 103 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 207 (accept_3_5 17 103 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 103 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 207 (accept_3_5 14 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 207 (Polychromatic418967fa.accept_21_12_19_18_1_7593 12 103 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 207 (accept_3_5 11 103 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 103 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 207 (accept_3_5 8 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 207 (Polychromatic418967fa.accept_21_7_19_18_1_7540 7 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 103 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 207 (accept_3_5 5 103 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 103 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 207
  (Polychromatic418967fa.accept_15_3_13_12_1_348 3 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 207 (accept_3_5 2 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 103 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  102 207 (allA_succ_of_accept 101 102 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 101 102 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 102 207 (Polychromatic418967fa.accept_12_4_6_3_1_332
  100 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 102 207 3 33 34 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 102 207
  (Polychromatic418967fa.accept_12_2_6_3_1_331 98 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 102 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 102 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 102 207 3 32 34 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 102 207 (Polychromatic418967fa.accept_10_5_2_7_1_345
  95 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 102 207
  (Polychromatic418967fa.accept_10_4_2_7_1_373 94 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 102 207 3 31 34 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 102 207 (Polychromatic418967fa.accept_12_8_6_3_1_366 92 102 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 102 207
  (Polychromatic418967fa.accept_14_7_4_11_1_3038 91 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 102 207 3 30 34 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 102 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 102 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 102 207 (Polychromatic418967fa.accept_12_4_6_3_1_332
  88 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 102 207 3 29 34 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 102 207
  (Polychromatic418967fa.accept_12_2_6_3_1_331 86 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 102 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 102 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 102 207 3 28 34 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 102 207 (Polychromatic418967fa.accept_11_6_3_9_1_906
  83 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 102 207
  (Polychromatic418967fa.accept_12_10_6_3_1_786 82 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 102 207 3 27 34 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 102 207 (Polychromatic418967fa.accept_12_8_6_3_1_366 80 102 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 102 207 (Polychromatic418967fa.accept_10_9_2_7_1_1096
  79 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 102 207 3 26 34 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 102 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 102 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 76 102 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 102 207 3 25 34 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 102 207 (Polychromatic418967fa.accept_10_4_2_7_1_373
  74 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 102 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 73 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 207 3 24 34 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 207 (Polychromatic418967fa.accept_14_1_4_11_1_3036 71 102 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 102 207
  (Polychromatic418967fa.accept_12_10_6_3_1_786 70 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 102 207 3 23 34 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 102 207 (Polychromatic418967fa.accept_12_8_6_3_1_366 68 102 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 102 207
  (Polychromatic418967fa.accept_19_10_7_17_1_9496 67 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 102 207 3 22 34 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 102 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 102 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 102 207
  (Polychromatic418967fa.accept_10_4_2_7_1_373 64 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 102 207 3 21 34 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 102 207 (Polychromatic418967fa.accept_12_2_6_3_1_331 62 102 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 102 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 61
  102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 102 207 3 20 34 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 102 207
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 59 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 102 207 (Polychromatic418967fa.accept_12_10_6_3_1_786 58 102 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 102 207 3 19 34 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 102 207 (Polychromatic418967fa.accept_12_8_6_3_1_366
  56 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 102 207
  (Polychromatic418967fa.accept_10_5_2_7_1_345 55 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 207 3 18 34 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 102 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 102 207 (Polychromatic418967fa.accept_12_4_6_3_1_332
  52 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 102 207 3 17 34 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 102 207
  (Polychromatic418967fa.accept_11_6_3_9_1_906 50 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 102 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 102 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 102 207 3 16 34 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 102 207 (Polychromatic418967fa.accept_18_11_12_9_1_992
  47 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 102 207
  (Polychromatic418967fa.accept_12_10_6_3_1_786 46 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 102 207 3 15 34 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 102 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 44 102 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 102 207
  (Polychromatic418967fa.accept_13_4_11_12_1_1318 43 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 102 207 3 14 34 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 102 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 102 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 102 207
  (Polychromatic418967fa.accept_12_4_6_3_1_332 40 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 102 207 3 13 34 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 102 207 (Polychromatic418967fa.accept_12_2_6_3_1_331 38 102 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 102 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 37
  102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 102 207 3 12 34 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 102 207
  (Polychromatic418967fa.accept_10_5_2_7_1_345 35 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 102 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 34 102 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 102 207 3 11 34 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 102 207 (Polychromatic418967fa.accept_12_8_6_3_1_366
  32 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 207
  (Polychromatic418967fa.accept_26_5_24_25_1_12092 31 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 102 207 3 10 34 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 102 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 102 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 102 207
  (Polychromatic418967fa.accept_11_6_3_9_1_906 28 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 102 207 3 9 34 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 102 207 (Polychromatic418967fa.accept_12_2_6_3_1_331 26 102 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 102 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 102 207 3 8 34 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 102 207
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 23 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 102 207 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 102 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 102 207 3 7 34 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 102 207
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 102 207 (Polychromatic418967fa.accept_10_9_2_7_1_1096 19 102 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 102 207 3 6 34 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 102 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 17
  102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 102 207
  (Polychromatic418967fa.accept_12_4_6_3_1_332 16 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 102 207 3 5 34 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 102 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 102 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 102 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 207 3 4 34 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 207
  (Polychromatic418967fa.accept_18_11_12_9_1_992 11 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 102 207 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 102 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 102 207 3 3 34 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 102 207 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 102 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 207
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 7 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 102 207 3 2 34 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 102 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 102 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 102 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 102 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 102 207 3 1 34 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 102 207
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 102 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 102 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 102 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 102
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 207 (allA_succ_of_accept 100 101 207 (accept_3_4 100 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 101 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 99 101 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 101 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 101 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 101 207 (accept_3_4 97 101 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 207 (Polychromatic418967fa.accept_10_6_1_7_1_342
  96 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 101 207
  (Polychromatic418967fa.accept_11_7_2_9_1_480 95 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 101 207 (accept_3_4 94 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 101 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 93 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 101 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 92 101 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 101 207 (accept_3_4 91 101 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 101 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 101 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 101 207
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 89 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 101 207 (accept_3_4 88 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 101 207 (Polychromatic418967fa.accept_13_9_10_12_1_2048 87 101 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 101 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 86
  101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 101 207 (accept_3_4 85
  101 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 101 207
  (Polychromatic418967fa.accept_10_4_1_7_1_371 84 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 101 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 83 101 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 101 207 (accept_3_4 82 101 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 101 207 (Polychromatic418967fa.accept_11_4_2_9_1_496 81 101 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 101 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 80 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 101 207 (accept_3_4 79 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 101 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 101 207 (Polychromatic418967fa.accept_14_7_3_11_1_2199 77 101 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 101 207 (accept_3_4 76 101 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 101 207 (Polychromatic418967fa.accept_17_7_16_3_1_4660 75 101
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 101 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 101 207 (accept_3_4 73 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 101 207 (Polychromatic418967fa.accept_13_7_10_12_1_2047 72 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 101 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 71 101 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 101 207 (accept_3_4 70 101 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 101 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 101 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 101 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 101 207 (accept_3_4 67 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 101 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 101 207 (Polychromatic418967fa.accept_16_1_5_15_1_2918 65 101 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 101 207 (accept_3_4 64 101 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 101 207 (Polychromatic418967fa.accept_13_11_10_12_1_1338 63
  101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 101 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 101 207 (accept_3_4 61 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 101 207 (Polychromatic418967fa.accept_13_8_10_12_1_1337 60 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 101 207 (Polychromatic418967fa.accept_11_4_2_9_1_496 59 101 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 101 207 (accept_3_4 58 101 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 101 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 101 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 101 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 101 207 (accept_3_4 55 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 101 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 101 207 (Polychromatic418967fa.accept_15_8_11_12_1_1626 53 101 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 101 207 (accept_3_4 52 101 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 101 207 (Polychromatic418967fa.accept_11_7_2_9_1_480 51 101
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 101 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 101 207 (accept_3_4 49 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 101 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 101 207 (Polychromatic418967fa.accept_13_8_10_12_1_1337 47 101 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 207 (accept_3_4 46 101 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 101
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 101 207 (accept_3_4 43 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 101 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 101 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 101 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 207 (accept_3_4 40 101 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 207 (Polychromatic418967fa.accept_25_14_1_7_1_12091 39 101 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 101 207 (accept_3_4 37 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 101 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 101 207 (Polychromatic418967fa.accept_13_9_10_12_1_2048 35 101 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 207 (accept_3_4 34 101 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 101
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 207 (accept_3_4 31 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 101 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 207 (accept_3_4 28 101 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 101 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 207 (accept_3_4 25 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 207 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 207 (Polychromatic418967fa.accept_15_8_11_12_1_1626 23 101 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 207 (accept_3_4 22 101 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 101
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 207 (accept_3_4 19 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 207 (Polychromatic418967fa.accept_16_1_5_15_1_2918 17 101 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 207 (accept_3_4 16 101 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 101 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 207 (accept_3_4 13 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 207 (Polychromatic418967fa.accept_18_12_11_9_1_4257 12 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 207 (Polychromatic418967fa.accept_13_11_10_12_1_1338 11 101 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 207 (accept_3_4 10 101 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 101 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 207 (accept_3_4 7 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 207 (Polychromatic418967fa.accept_36_5_29_27_1_12090 5 101 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 207 (accept_3_4 4 101 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 207 (Polychromatic418967fa.accept_19_3_6_17_1_6579 3 101
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 207 (accept_3_4 1 101 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  100 207 (allA_succ_of_accept 99 100 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 99 100 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 100 207 (accept_3_5 98 100 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 100 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 97 100 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 100 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 96 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 100 207 (accept_3_5 95 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 100 207 (Polychromatic418967fa.accept_13_3_9_12_1_2062 94 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 100 207 (Polychromatic418967fa.accept_14_9_2_11_1_780 93 100 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 100 207 (accept_3_5 92 100 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 100 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 100 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 100 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 90 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 100 207 (accept_3_5 89 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 100 207 (Polychromatic418967fa.accept_13_10_9_12_1_2814 88 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 100 207 (Polychromatic418967fa.accept_11_10_1_9_1_2060 87 100 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 100 207 (accept_3_5 86 100 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 100 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 100 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 100 207
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 84 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 100 207 (accept_3_5 83 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 100 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 82 100 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 100 207 (Polychromatic418967fa.accept_13_3_9_12_1_2062 81 100
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 100 207 (accept_3_5 80 100
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 100 207
  (Polychromatic418967fa.accept_6_1_4_3_1_14 79 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 100 207 (Polychromatic418967fa.accept_12_6_4_3_1_361 78 100 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 100 207 (accept_3_5 77 100 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 100 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 76 100 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 100 207 (Polychromatic418967fa.accept_7_5_2_4_1_126
  75 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 100 207 (accept_3_5 74
  100 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 100 207
  (Polychromatic418967fa.accept_6_1_4_3_1_14 73 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 100 207 (Polychromatic418967fa.accept_16_8_4_15_1_2941 72 100 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 100 207 (accept_3_5 71 100 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 100 207 (Polychromatic418967fa.accept_27_16_19_18_1_12089 70 100 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 100 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 69 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 100 207 (accept_3_5 68 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 100 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 100 207 (Polychromatic418967fa.accept_12_6_4_3_1_361 66 100 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 100 207 (accept_3_5 65 100 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 100 207 (Polychromatic418967fa.accept_19_7_5_17_1_3849 64 100
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 100 207
  (Polychromatic418967fa.accept_17_12_15_3_1_7168 63 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 100 207 (accept_3_5 62 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 100 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 100 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 100 207 (Polychromatic418967fa.accept_13_8_9_12_1_2813 60 100
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 100 207 (accept_3_5 59 100
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 100 207
  (Polychromatic418967fa.accept_15_13_10_12_1_2503 58 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 100 207 (Polychromatic418967fa.accept_21_15_16_18_1_7529 57 100 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 100 207 (accept_3_5 56 100 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 100 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 100 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 100 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 54 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 100 207 (accept_3_5 53 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 100 207 (Polychromatic418967fa.accept_15_7_10_12_1_2403 52 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 100 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 100 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 100 207 (accept_3_5 50 100 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 100 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 100 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 100 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 100 207 (accept_3_5 47 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 100 207 (Polychromatic418967fa.accept_16_14_4_15_1_3944 46 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 100 207 (Polychromatic418967fa.accept_19_7_5_17_1_3849 45 100 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 100 207 (accept_3_5 44 100 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 100 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 100 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 100 207
  (Polychromatic418967fa.accept_12_6_4_3_1_361 42 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 100 207 (accept_3_5 41 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 100 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 100 207 (Polychromatic418967fa.accept_15_9_10_12_1_1625 39 100 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 100 207 (accept_3_5 38 100 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 100 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 100 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 100 207
  (Polychromatic418967fa.accept_13_10_9_12_1_2814 36 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 100 207 (accept_3_5 35 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 100 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 100 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 100 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 100 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 100 207 (accept_3_5 32 100 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 100 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 31
  100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 100 207
  (Polychromatic418967fa.accept_12_6_4_3_1_361 30 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 100 207 (accept_3_5 29 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 100 207 (Polychromatic418967fa.accept_15_13_10_12_1_2503 28 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 100 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 100 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 100 207 (accept_3_5 26 100 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 100 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 100 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 100 207
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 24 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 100 207 (accept_3_5 23 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 100 207 (Polychromatic418967fa.accept_15_7_10_12_1_2403 22 100 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 100 207
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 100 207 (accept_3_5 20 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 100 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 100 207 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 100 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 100 207 (accept_3_5 17 100 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 100 207 (Polychromatic418967fa.accept_13_3_9_12_1_2062 16 100
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 100 207
  (Polychromatic418967fa.accept_18_15_10_9_1_2009 15 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 100 207 (accept_3_5 14 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 100 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 100 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 100 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 100 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 100 207 (accept_3_5 11 100 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 100 207
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 10 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 100 207 (Polychromatic418967fa.accept_14_9_2_11_1_780 9 100 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 100 207 (accept_3_5 8 100 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 100 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 100 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 100 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 6
  100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 100 207 (accept_3_5 5 100
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 100 207
  (Polychromatic418967fa.accept_26_4_22_25_1_12088 4 100 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 100 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 100 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 100 207 (accept_3_5 2 100 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 100 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 100 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_207_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


